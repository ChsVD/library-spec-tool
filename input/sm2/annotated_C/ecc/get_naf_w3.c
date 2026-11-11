/* Verification copy of YCrypt/sm2/ecc.c::get_naf_w3. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ Extern Coq
      (Z::pow : Z -> Z -> Z)
      (wnaf3_digit : Z -> Prop)
      (wnaf3_value : list Z -> Z)
      (wnaf3_separated : list Z -> Prop)
 */

u32* memcpy(u32* dest, void* src, size_t n)
/*@ from_fn
    With X
    Require
      n == 32 &&
      store_fn(src, X) *
      UndefStructPredu32(dest)
    Ensure
      __return == dest &&
      store_fn(src, X) *
      store_u256(dest, X)
 */;

void u32_sub(const u32* a, const u32* b, u32* result)
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      exists S borrow,
        0 <= S && S < U256_MOD &&
        0 <= borrow && borrow <= 1 &&
        A - B == S - borrow * U256_MOD &&
        result == a &&
        store_u256(result, S) *
        store_u256(b, B)
 */;

u1 u32_add(const u32* a, const u32* b, u32* result)
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
 */;

void u32_shr(u32 *input)
/*@ With (X : Z)
    Require store_u256(input, X)
    Ensure store_u256(input, X / 2)
 */;

// Computing the NAF of a positive integer k
// w = 3
void get_naf_w3(const u32* pk, int8_t naf_w3[257])
/*@ non_alias
    With (K : Z)
    Require
      store_fn(pk, K) *
      CharArray::undef_full(naf_w3, 257)
    Ensure
      store_fn(pk, K) *
      store_wnaf3(naf_w3, K)
 */
/*@ non_alias */
{
	int i = 0;
	int8_t ki;
	u32 x = { 0 }, k;

	memcpy(&k, pk, sizeof(k));
	/*@ Inv Assert
	    exists digits Kcur X,
	      pk == pk@pre && naf_w3 == naf_w3@pre &&
	      0 <= i && i <= 257 &&
	      i == Zlength(digits) &&
	      0 <= Kcur &&
	      (i <= 256 => Kcur <= Z::pow(2, 256 - i)) &&
	      (i >= 257 => Kcur == 0) &&
	      K == wnaf3_value(digits) + Kcur * Z::pow(2, i) &&
	      (forall (j : Z),
	        0 <= j && j < i => wnaf3_digit(Znth(j, digits, 0))) &&
	      wnaf3_separated(digits) &&
	      (i >= 1 && Znth(i - 1, digits, 0) != 0 => Kcur % 4 == 0) &&
	      (i >= 2 && Znth(i - 2, digits, 0) != 0 => Kcur % 2 == 0) &&
	      0 <= X && X < U64_MOD &&
	      store_fn(pk@pre, K) *
	      store_u256(&k, Kcur) *
	      store_u256(&x, X) *
	      has_permission(&ki) *
	      CharArray::full(naf_w3@pre, i, digits) *
	      CharArray::undef_seg(naf_w3@pre, i, 257)
	*/
	for (i = 0; i < 257; i++)
	{
		/*@ do open_store_u256 */
		ki = ((int8_t)(k.v[0])) & 0x7;   // k mod (2^3)

										  //naf_w3[i] = ki;
		if ((ki & 1) != 0)  // k is odd
		{
			if (ki >= 4) // -2^2 < ki < 2^2
			{
				ki -= 8; // ki - 2^3
			}
			if (ki >= 0)
			{
				/*@ do open_store_u256 */
				x.v[0] = ki;
				u32_sub(&k, &x, &k);
			}
			else  // ki < 0
			{
				/*@ do open_store_u256 */
				x.v[0] = -ki;
				u32_add(&k, &x, &k);
			}
			naf_w3[i] = ki;
		}
		else
		{
			naf_w3[i] = 0;
		}
		u32_shr(&k);   // k = k / 2
	}
}
