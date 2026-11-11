/*
 * Verification extraction of YCrypt solinas_reduce.
 *
 * The function implementation follows bignumber/YCrypt/sm2/fieldOp.c.
 */

#include "../include/fieldOp.h"
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
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      exists S,
        0 <= S && S < U256_MOD &&
        0 <= __return && __return <= 1 &&
        A + B == S + __return * U256_MOD &&
        result == b &&
        store_u256(a, A) *
        store_u256(result, S)
 */
;

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

#define JIA
void solinas_reduce(const u8 input[8], u32* result)
/*@ non_alias
    With T
    Require
      0 <= T && T < U512_MOD &&
      store_u64_limbs(input, 8, T) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        T == Zout + K * SM2_P_Z &&
        store_u64_limbs(input, 8, T) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ non_alias */
{
	/*@ do open_store_u64_limbs */
#ifdef JIA
	// fast reduction 512bit to 256bit
	// ref: http://cacr.uwaterloo.ca/techreports/1999/corr99-39.pdf
	u1 carry;
	u32 sumD;
	u4* A = (u4*)input;
	/*@
	  store_u64_limbs(input, 8, T)
	  which implies
	  exists words16,
		    Zlength(words16) == 16 &&
		    u32_list_bounded(words16) &&
		    u32_list_value(words16) == T &&
		    UIntArray::full(input, 16, words16)
		 */
	u8 acc = (u8)A[14] + A[15];
	u8 b1tmp = acc; // acc = A[14] + A[15]
	sumD.v[3] = acc + A[11];
	acc += A[13];
	u8 b0tmp = acc;
	u8 b5tmp = acc + A[10] + A[15];
	acc += A[12]; // acc = A[14] + A[15] + A[13] + A[12]
	sumD.v[2] = acc + A[9] + A[14];
	u8 b7tmp = acc + A[15];
	acc += A[11]; // acc = A[14] + A[15] + A[13] + A[12] + A[11]
	u8 b3tmp = acc + A[8] + A[13];
	u8 minus = (u8)A[8] + A[9] + A[13] + A[14];
	carry = portable_addcarryx_u64(0, sumD.v[2], (b3tmp >> 32) | (b5tmp << 32), &sumD.v[2]);
	portable_addcarryx_u64(carry, sumD.v[3], b5tmp >> 32, &sumD.v[3]); /// may be overflow?
	acc += (u8)A[9] + A[10]; // acc = A[14] + A[15] + A[13] + A[12] + A[11] + A[9] + A[10]
	b1tmp += acc;
	acc += A[8]; // acc = A[14] + A[15] + A[13] + A[12] + A[11] + A[9] + A[10] + A[8]
	b0tmp += acc;
	b7tmp += acc;
	carry = portable_addcarryx_u64(0, b0tmp, b1tmp << 32, &sumD.v[0]);
	portable_addcarryx_u64(carry, b1tmp >> 32, b3tmp << 32, &sumD.v[1]);
	carry = portable_addcarryx_u64(0, sumD.v[3], b7tmp << 32, &sumD.v[3]);
	portable_addcarryx_u64(carry, b7tmp >> 32, 0, &acc);

	// u8 B[8] = {
	// 	0, 0, A[15],  // B[2] is temp
	// 	(u8)A[8] + A[13], (u8)A[9] + A[14], (u8)A[10] + A[15], A[11], A[15]
	// };
	// B[2] += A[14]; B[1] += B[2]; B[6] += B[2];
	// B[2] += A[13]; B[0] += B[2]; B[5] += B[2];
	// B[2] += A[12]; B[4] += B[2]; B[7] += B[2];
	// B[2] += A[11]; B[3] += B[2];
	// B[2] += (u8)A[9] + A[10]; B[1] += B[2];
	// B[2] += A[8]; B[0] += B[2]; B[7] += B[2];

		/*@
		  exists words16,
		    Zlength(words16) == 16 &&
			    u32_list_bounded(words16) &&
			    u32_list_value(words16) == T &&
		    UIntArray::full(input, 16, words16)
		  which implies
		  exists limbs8,
			    Zlength(limbs8) == 8 &&
			    u64_list_bounded(limbs8) &&
			    u64_list_value(limbs8) == T &&
				    UInt64Array::full(input, 8, limbs8)
			 */
			u32 S = { input[0], input[1], input[2], input[3] };
			/*@ do normalize_u64_reads */
			carry = u32_add(&S, &sumD, &S) /*@ where (r_eq_a) */;
		portable_addcarryx_u64(carry, acc, 0, &acc);

		u8 tmp = acc << 32;
		u32 payload = {
			acc,        // acc * SM2_rhoP.v[0]
			tmp - acc,  // acc * SM2_rhoP.v[1],
			0,          // acc * SM2_rhoP.v[2],
			tmp         // acc * SM2_rhoP.v[3]
		};
		carry = u32_add(&payload, &S, &S) /*@ where (r_eq_b) */;
		/*@ Assert
		      exists Sraw SDred Pred Kred C,
		        input == input@pre &&
		        result == result@pre &&
		        0 <= T && T < U512_MOD &&
		        0 <= Sraw && Sraw < U256_MOD &&
		        0 <= C && C <= 1 &&
		        0 <= Sraw + C * SM2_RHOP_Z &&
		        Sraw + C * SM2_RHOP_Z < U256_MOD &&
		        0 <= minus && minus <= SOLINAS_MINUS_MAX &&
		        T == Sraw + C * SM2_RHOP_Z - minus * U64_MOD +
		             Kred * SM2_P_Z &&
		        store_u64_limbs(input, 8, T) *
		        store_u256(&sumD, SDred) *
		        store_u256(&S, Sraw) *
		        store_u256(&payload, Pred) *
		        UInt64Array::undef_full(&(result->v[0]), 4) *
		        store_sm2_p *
		        store_sm2_rhop *
		        store(&carry, unsigned char, C) *
		        has_permission(&A) *
		        has_permission(&b1tmp) *
		        has_permission(&acc) *
		        has_permission(&b0tmp) *
		        has_permission(&b5tmp) *
		        has_permission(&b7tmp) *
		        has_permission(&b3tmp) *
		        has_permission(&tmp)
		 */
		if (carry) {
			/*@ do open_sm2_rhop */
			/*@ do open_store_u256 */
			u32_add(&SM2_rhoP, &S, &S) /*@ where (r_eq_b) */;
		}
	/*@ Branch join all with Assert
		  exists Sred SDred Pred Kred,
		    input == input@pre &&
		    result == result@pre &&
		    0 <= T && T < U512_MOD &&
	    0 <= Sred && Sred < U256_MOD &&
	    0 <= minus && minus <= SOLINAS_MINUS_MAX &&
	    T == Sred - minus * U64_MOD + Kred * SM2_P_Z &&
	    store_u64_limbs(input, 8, T) *
	    store_u256(&sumD, SDred) *
	    store_u256(&S, Sred) *
	    store_u256(&payload, Pred) *
	    UInt64Array::undef_full(&(result->v[0]), 4) *
	    store_sm2_p *
	    store_sm2_rhop *
	    has_permission(&carry) *
	    has_permission(&A) *
	    has_permission(&b1tmp) *
	    has_permission(&acc) *
	    has_permission(&b0tmp) *
	    has_permission(&b5tmp) *
	    has_permission(&b7tmp) *
	    has_permission(&b3tmp) *
	    has_permission(&tmp)
	 */
	/*@ do open_store_u256 */
	// inverse add one
	result->v[0] = S.v[0];
	carry = portable_addcarryx_u64(1, S.v[1], ~minus, &result->v[1]);
	carry = portable_addcarryx_u64(carry, S.v[2], 0xFFFFFFFFFFFFFFFF, &result->v[2]);
	carry = portable_addcarryx_u64(carry, S.v[3], 0xFFFFFFFFFFFFFFFF, &result->v[3]);
	/*@ do open_sm2_rhop */
	/*@ do open_sm2_p */
	/*@ do open_store_u256 */
	if (!carry) {
		u32_sub(result, &SM2_rhoP, result) /*@ where (r_eq_a) */;
	}
	if (u32_ge(result, &SM2_P)) {
		u32_add(result, &SM2_rhoP, result) /*@ where (r_eq_a) */;
	}

#else
	// fast reduction 256bit to 128bit
	// ref: http://cacr.uwaterloo.ca/techreports/1999/corr99-39.pdf

	u4 * A = (u4 *)(input);
	u8 B[8] = {
		0, 0, A[15],  // B[2] is temp
		(u8)A[8] + A[13], (u8)A[9] + A[14], (u8)A[10] + A[15], A[11], A[15]
	};
	B[2] += A[14]; B[1] += B[2]; B[6] += B[2];
	B[2] += A[13]; B[0] += B[2]; B[5] += B[2];
	B[2] += A[12]; B[4] += B[2]; B[7] += B[2];
	B[2] += A[11]; B[3] += B[2];
	B[2] += (u8)A[9] + A[10]; B[1] += B[2];
	B[2] += A[8]; B[0] += B[2]; B[7] += B[2];

	u32 sumD;
	u4* ptr = (u4*)sumD.v;
	ptr[0] = (u4)B[0];
	B[1] += B[0] >> 32;
	ptr[1] = (u4)B[1];
	ptr[2] = (u4)(B[1] >> 32);
	ptr[3] = (u4)B[3];
	B[4] += B[3] >> 32;
	ptr[4] = (u4)B[4];
	B[5] += B[4] >> 32;
	ptr[5] = (u4)B[5];
	B[6] += B[5] >> 32;
	ptr[6] = (u4)B[6];
	B[7] += B[6] >> 32;
	ptr[7] = (u4)B[7];
	u1 carry = (u1)(B[7] >> 32);

	u32 S = { input[0], input[1], input[2], input[3] };
	carry += u32_add(&S, &sumD, &S) /*@ where (r_eq_a) */;
	u32 payload = { carry*SM2_rhoP.v[0], carry*SM2_rhoP.v[1], carry*SM2_rhoP.v[2], carry*SM2_rhoP.v[3] };
	carry = u32_add(&payload, &S, &S) /*@ where (r_eq_b) */;
	while (carry) {
		carry = u32_add(&SM2_rhoP, &S, &S) /*@ where (r_eq_b) */;
	}

	result.v[0] = result.v[2] = result.v[3] = 0;
	result.v[1] = (u8)A[8] + A[9] + A[13] + A[14];
	sub_mod_p(S, result, result);

#endif // JIA

}
