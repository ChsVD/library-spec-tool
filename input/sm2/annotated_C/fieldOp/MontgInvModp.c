/* Verification copy of YCrypt/sm2/fieldOp.c::MontgInvModp. */

#include "../include/fieldOp.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/sm2_constants.strategies" */

typedef unsigned char uint8_t;

u32* memcpy(u32* dest, void* src, size_t n)
/*@ from_fp
    With X
    Require
      n == 32 &&
      store_fp(src, X) *
      UndefStructPredu32(dest)
    Ensure
      __return == dest &&
      store_fp(src, X) *
      store_u256(dest, X)
 */
/*@ from_u256
    With X
    Require
      n == 32 &&
      store_u256(src, X) *
      UndefStructPredu32(dest)
    Ensure
      __return == dest &&
      store_u256(src, X) *
      store_u256(dest, X)
 */
/*@ from_sm2_p
    Require
      n == 32 &&
      src == &(SM2_P.v[0]) &&
      store_sm2_p *
      UndefStructPredu32(dest)
    Ensure
      __return == dest &&
      src == &(SM2_P.v[0]) &&
      store_sm2_p *
      store_u256(dest, SM2_P_Z)
 */
;

u32* memset(u32* dest, int c, size_t n)
/*@ Require
      c == 0 && n == 32 &&
      UndefStructPredu32(dest)
    Ensure
      __return == dest &&
      store_u256(dest, 0)
 */
;

bool u32_eq_zero(const u32* a)
/*@ With A
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) ||
       (__return == 0 && A != 0)) &&
      store_u256(a, A)
 */
;

bool u32_gr(const u32* a, const u32* b)
/*@ With A B
    Require
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A > B) ||
       (__return == 0 && A <= B)) &&
      store_u256(a, A) *
      store_u256(b, B)
 */
;

bool u32_ge(const u32* a, const u32* b)
/*@ With A B
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

void u32_shr(u32* input)
/*@ With X
    Require
      store_u256(input, X)
    Ensure
      store_u256(input, X / 2)
 */
;

u1 u32_shl(u32* input)
/*@ With X
    Require
      store_u256(input, X)
    Ensure
      exists Y,
        u256_shl_result(X, Y, __return) &&
        store_u256(input, Y)
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
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      exists S borrow,
        0 <= S && S < U256_MOD &&
        0 <= borrow && borrow <= 1 &&
        A - B == S - borrow * U256_MOD &&
        result == b &&
        store_u256(a, A) *
        store_u256(result, S)
 */
;

void montg_mul_mod_p(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_u256(x, X) *
      store_u256(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists R K,
        0 <= R && R < SM2_P_Z &&
        R * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_u256(y, Y) *
        store_fp(result, R) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void MontgInvModp(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      A != 0 &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Z K,
        0 <= Z && Z < SM2_P_Z &&
        A * Z == U256_MOD + K * SM2_P_Z &&
        store_fp(a, A) *
        store_fp(result, Z) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ in_place
    With A
    Require
      result == a &&
      A != 0 &&
      store_fp(a, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Z K,
        result == a &&
        0 <= Z && Z < SM2_P_Z &&
        A * Z == U256_MOD + K * SM2_P_Z &&
        store_fp(result, Z) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void MontgInvModp(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      A != 0 &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv,
        0 <= Ainv && Ainv < SM2_P_Z &&
        Zmod(A * Ainv, SM2_P_Z) == 1 &&
        store_fp(a, A) *
        store_fp(result, mont_p(Ainv)) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void MontgInvModp(const u32 *a, u32 *result)
/*@ mont_in_place <= in_place
    With A
    Require
      result == a &&
      A != 0 &&
      store_fp(a, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv,
        result == a &&
        0 <= Ainv && Ainv < SM2_P_Z &&
        Zmod(A * Ainv, SM2_P_Z) == 1 &&
        store_fp(result, mont_p(Ainv)) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void MontgInvModp(const u32 *a, u32 *result)
/*@ non_alias */
/*@ in_place */
{
	u32 u, v, r, s, t;
	UINT64 k = 0;
	UINT64 i = 0;
	uint8_t carry = 0;

	// Phase I  -> Get r and k
	memcpy(&u, SM2_P.v, 32)
	/*@
	  where (from_sm2_p)
	    $ non_alias
	  where (from_sm2_p)
	    $ in_place
	 */;
	memcpy(&v, a, 32)
	/*@
	  where (from_fp) X = A_non_alias
	    $ non_alias
	  where (from_fp) X = A_in_place
	    $ in_place
	 */;
	memset(&r, 0, 32);
	memset(&s, 0, 32);
	/*@ do open_store_u256 */
	s.v[0] = 1; // s = 1

	/*@ Inv
	  non_alias: Assert
	  exists Un Vn Rn Sn,
	    a == a@pre && result == result@pre && i == 0 &&
	    sm2p_mont_inv_phase1_state(A_non_alias, Un, Vn, Rn, Sn, k, carry) &&
	    store_fp(a, A_non_alias) *
	    UndefStructPredu32(result) *
	    store_sm2_p *
	    store_u256(&u, Un) * store_u256(&v, Vn) *
	    store_u256(&r, Rn) * store_u256(&s, Sn) *
	    UndefStructPredu32(&t) *
	    store_sm2_rhop;
	  in_place: Assert
	  exists Ui Vi Ri Si,
	    a == a@pre && result == result@pre && result == a && i == 0 &&
	    sm2p_mont_inv_phase1_state(A_in_place, Ui, Vi, Ri, Si, k, carry) &&
	    store_fp(a, A_in_place) *
	    store_sm2_p *
	    store_u256(&u, Ui) * store_u256(&v, Vi) *
	    store_u256(&r, Ri) * store_u256(&s, Si) *
	    UndefStructPredu32(&t) *
	    store_sm2_rhop
	 */
	while (!u32_eq_zero(&v))  // v > 0
	{
		/*@ Given Un Vn Rn Sn $ non_alias */
		/*@ Given Ui Vi Ri Si $ in_place */
		/*@ do open_store_u256 */
		if ((u.v[0] & 1) == 0)    // u is even
		{
			u32_shr(&u);     // u = u / 2
			u32_shl(&s);     // s = 2s
			/*@ Assert
			  exists S2,
			    a == a@pre && result == result@pre && i == 0 &&
			    sm2p_mont_inv_phase1_state(A_non_alias, Un, Vn,
			      Rn, Sn, k, carry) &&
			    sm2p_mont_inv_phase1_state(A_non_alias, Un / 2, Vn,
			      Rn, S2, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
			    store_sm2_p * store_u256(&u, Un / 2) *
			    store_u256(&v, Vn) * store_u256(&r, Rn) *
			    store_u256(&s, S2) * UndefStructPredu32(&t) *
			    store_sm2_rhop
			    $ non_alias
			 */
			/*@ Assert
			  exists S2,
			    a == a@pre && result == result@pre && result == a && i == 0 &&
			    sm2p_mont_inv_phase1_state(A_in_place, Ui, Vi,
			      Ri, Si, k, carry) &&
			    sm2p_mont_inv_phase1_state(A_in_place, Ui / 2, Vi,
			      Ri, S2, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_in_place) * store_sm2_p *
			    store_u256(&u, Ui / 2) * store_u256(&v, Vi) *
			    store_u256(&r, Ri) * store_u256(&s, S2) *
			    UndefStructPredu32(&t) * store_sm2_rhop
			    $ in_place
			 */
		}
		else if ((v.v[0] & 1) == 0)  // v is even
		{
			u32_shr(&v);     // v = v / 2
			u32_shl(&r);     // r = 2r
			/*@ Assert
			  exists R2n,
			    a == a@pre && result == result@pre && i == 0 &&
			    sm2p_mont_inv_phase1_state(A_non_alias, Un, Vn,
			      Rn, Sn, k, carry) &&
			    sm2p_mont_inv_phase1_state(A_non_alias, Un, Vn / 2,
			      R2n, Sn, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
			    store_sm2_p * store_u256(&u, Un) *
			    store_u256(&v, Vn / 2) * store_u256(&r, R2n) *
			    store_u256(&s, Sn) * UndefStructPredu32(&t) *
			    store_sm2_rhop
			    $ non_alias
			 */
			/*@ Assert
			  exists R2i,
			    a == a@pre && result == result@pre && result == a && i == 0 &&
			    sm2p_mont_inv_phase1_state(A_in_place, Ui, Vi,
			      Ri, Si, k, carry) &&
			    sm2p_mont_inv_phase1_state(A_in_place, Ui, Vi / 2,
			      R2i, Si, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_in_place) * store_sm2_p *
			    store_u256(&u, Ui) * store_u256(&v, Vi / 2) *
			    store_u256(&r, R2i) * store_u256(&s, Si) *
			    UndefStructPredu32(&t) * store_sm2_rhop
			    $ in_place
			 */
		}
		else if (u32_gr(&u, &v))  // u > v
		{
			u32_sub(&u, &v, &u)
			/*@
			  where (r_eq_a) A = Un, B = Vn
			    $ non_alias
			  where (r_eq_a) A = Ui, B = Vi
			    $ in_place
			 */;  // u = u - v
			u32_shr(&u);        // u = u / 2

			u32_add(&r, &s, &r)
			/*@
			  where (r_eq_a) A = Rn, B = Sn
			    $ non_alias
			  where (r_eq_a) A = Ri, B = Si
			    $ in_place
			 */;  // r = r + s
			u32_shl(&s);        // s = 2s
			/*@ Assert
			  exists Usub borrow Rsum add_carry S2,
			    a == a@pre && result == result@pre && i == 0 &&
			    Un > Vn &&
			    0 <= Usub && Usub < U256_MOD &&
			    0 <= borrow && borrow <= 1 &&
			    Un - Vn == Usub - borrow * U256_MOD &&
			    0 <= Rsum && Rsum < U256_MOD &&
			    0 <= add_carry && add_carry <= 1 &&
			    Rn + Sn == Rsum + add_carry * U256_MOD &&
			    sm2p_mont_inv_phase1_state(A_non_alias, Un, Vn,
			      Rn, Sn, k, carry) &&
			    sm2p_mont_inv_phase1_state(A_non_alias, Usub / 2, Vn,
			      Rsum, S2, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
			    store_sm2_p * store_u256(&u, Usub / 2) *
			    store_u256(&v, Vn) * store_u256(&r, Rsum) *
			    store_u256(&s, S2) * UndefStructPredu32(&t) *
			    store_sm2_rhop
			    $ non_alias
			 */
			/*@ Assert
			  exists Usub borrow Rsum add_carry S2,
			    a == a@pre && result == result@pre && result == a && i == 0 &&
			    Ui > Vi &&
			    0 <= Usub && Usub < U256_MOD &&
			    0 <= borrow && borrow <= 1 &&
			    Ui - Vi == Usub - borrow * U256_MOD &&
			    0 <= Rsum && Rsum < U256_MOD &&
			    0 <= add_carry && add_carry <= 1 &&
			    Ri + Si == Rsum + add_carry * U256_MOD &&
			    sm2p_mont_inv_phase1_state(A_in_place, Ui, Vi,
			      Ri, Si, k, carry) &&
			    sm2p_mont_inv_phase1_state(A_in_place, Usub / 2, Vi,
			      Rsum, S2, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_in_place) * store_sm2_p *
			    store_u256(&u, Usub / 2) * store_u256(&v, Vi) *
			    store_u256(&r, Rsum) * store_u256(&s, S2) *
			    UndefStructPredu32(&t) * store_sm2_rhop
			    $ in_place
			 */
		}
		else// if (u32_ge(v, u))  // v >= u
		{
			u32_sub(&v, &u, &v)
			/*@
			  where (r_eq_a) A = Vn, B = Un
			    $ non_alias
			  where (r_eq_a) A = Vi, B = Ui
			    $ in_place
			 */;  // v = v - u
			u32_shr(&v);        // v = v / 2

			u32_add(&r, &s, &s)
			/*@
			  where (r_eq_b) A = Rn, B = Sn
			    $ non_alias
			  where (r_eq_b) A = Ri, B = Si
			    $ in_place
			 */;  // s = r + s
			carry += u32_shl(&r);        // r = 2r, r may by overflow at the last time
			/*@ Assert
			  exists Vsub borrow Ssum add_carry R2n,
			    a == a@pre && result == result@pre && i == 0 &&
			    Un <= Vn &&
			    0 <= Vsub && Vsub < U256_MOD &&
			    0 <= borrow && borrow <= 1 &&
			    Vn - Un == Vsub - borrow * U256_MOD &&
			    0 <= Ssum && Ssum < U256_MOD &&
			    0 <= add_carry && add_carry <= 1 &&
			    Rn + Sn == Ssum + add_carry * U256_MOD &&
			    sm2p_mont_inv_phase1_state(A_non_alias, Un, Vsub / 2,
			      R2n, Ssum, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
			    store_sm2_p * store_u256(&u, Un) *
			    store_u256(&v, Vsub / 2) * store_u256(&r, R2n) *
			    store_u256(&s, Ssum) * UndefStructPredu32(&t) *
			    store_sm2_rhop
			    $ non_alias
			 */
			/*@ Assert
			  exists Vsub borrow Ssum add_carry R2i,
			    a == a@pre && result == result@pre && result == a && i == 0 &&
			    Ui <= Vi &&
			    0 <= Vsub && Vsub < U256_MOD &&
			    0 <= borrow && borrow <= 1 &&
			    Vi - Ui == Vsub - borrow * U256_MOD &&
			    0 <= Ssum && Ssum < U256_MOD &&
			    0 <= add_carry && add_carry <= 1 &&
			    Ri + Si == Ssum + add_carry * U256_MOD &&
			    sm2p_mont_inv_phase1_state(A_in_place, Ui, Vsub / 2,
			      R2i, Ssum, unsigned_last_nbits(k + 1, 64), carry) &&
			    store_fp(a, A_in_place) * store_sm2_p *
			    store_u256(&u, Ui) * store_u256(&v, Vsub / 2) *
			    store_u256(&r, R2i) * store_u256(&s, Ssum) *
			    UndefStructPredu32(&t) * store_sm2_rhop
			    $ in_place
			 */
		}
		k++;                   // k = k + 1
	}

	/*@ Assert
	  exists Un Rn Sn,
	    a == a@pre && result == result@pre && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    sm2p_mont_inv_phase1_state(A_non_alias, Un, 0, Rn, Sn, k, carry) &&
	    sm2p_mont_inv_phase1_exit_carry(A_non_alias, Rn, k, carry) &&
	    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
	    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
	    store_u256(&r, Rn) * store_u256(&s, Sn) * UndefStructPredu32(&t) *
	    store_sm2_rhop
	    $ non_alias
	 */
	/*@ Assert
	  exists Ui Ri Si,
	    a == a@pre && result == result@pre && result == a && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    sm2p_mont_inv_phase1_state(A_in_place, Ui, 0, Ri, Si, k, carry) &&
	    sm2p_mont_inv_phase1_exit_carry(A_in_place, Ri, k, carry) &&
	    store_fp(a, A_in_place) * store_sm2_p *
	    store_u256(&u, Ui) * store_u256(&v, 0) *
	    store_u256(&r, Ri) * store_u256(&s, Si) * UndefStructPredu32(&t) *
	    store_sm2_rhop
	    $ in_place
	 */
	/*@ Given Un Rn Sn $ non_alias */
	/*@ Given Ui Ri Si $ in_place */

	if (carry > 0)  // This step is important
	{
		/*@ do open_sm2_p */
		/*@ do open_store_u256 */
		u32_sub(&r, &SM2_P, &r)
		/*@
		  where (r_eq_a) A = Rn, B = SM2_P_Z
		    $ non_alias
		  where (r_eq_a) A = Ri, B = SM2_P_Z
		    $ in_place
		 */;
		/*@ Assert
		  exists R1,
		    a == a@pre && result == result@pre && i == 0 &&
		    0 < carry && carry <= 1 && 256 <= k && k <= 512 &&
		    sm2p_mont_inv_post_loop_residue(A_non_alias, R1, k) &&
		    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
		    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		    store_u256(&r, R1) * store_u256(&s, Sn) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ non_alias
		 */
		/*@ Assert
		  exists R1,
		    a == a@pre && result == result@pre && result == a && i == 0 &&
		    0 < carry && carry <= 1 && 256 <= k && k <= 512 &&
		    sm2p_mont_inv_post_loop_residue(A_in_place, R1, k) &&
		    store_fp(a, A_in_place) * store_sm2_p *
		    store_u256(&u, Ui) * store_u256(&v, 0) *
		    store_u256(&r, R1) * store_u256(&s, Si) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ in_place
		 */
	}
	/*@ Assert
	  exists R2n,
	    a == a@pre && result == result@pre && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    sm2p_mont_inv_post_loop_residue(A_non_alias, R2n, k) &&
	    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
	    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
	    store_u256(&r, R2n) * store_u256(&s, Sn) *
	    UndefStructPredu32(&t) * store_sm2_rhop
	    $ non_alias
	 */
	/*@ Assert
	  exists R2i,
	    a == a@pre && result == result@pre && result == a && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    sm2p_mont_inv_post_loop_residue(A_in_place, R2i, k) &&
	    store_fp(a, A_in_place) * store_sm2_p *
	    store_u256(&u, Ui) * store_u256(&v, 0) *
	    store_u256(&r, R2i) * store_u256(&s, Si) *
	    UndefStructPredu32(&t) * store_sm2_rhop
	    $ in_place
	 */
	/*@ Given R2n $ non_alias */
	/*@ Given R2i $ in_place */
	/*@ do open_sm2_p */
	/*@ do open_store_u256 */
	if (u32_ge(&r, &SM2_P))
	{
		/*@ do open_store_u256 */
		u32_sub(&r, &SM2_P, &r)
		/*@
		  where (r_eq_a) A = R2n, B = SM2_P_Z
		    $ non_alias
		  where (r_eq_a) A = R2i, B = SM2_P_Z
		    $ in_place
		 */;
		/*@ Assert
		  exists R3,
		    a == a@pre && result == result@pre && i == 0 &&
		    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
		    sm2p_mont_inv_post_loop_norm(A_non_alias, R3, k) &&
		    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
		    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		    store_u256(&r, R3) * store_u256(&s, Sn) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ non_alias
		 */
		/*@ Assert
		  exists R3,
		    a == a@pre && result == result@pre && result == a && i == 0 &&
		    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
		    sm2p_mont_inv_post_loop_norm(A_in_place, R3, k) &&
		    store_fp(a, A_in_place) * store_sm2_p *
		    store_u256(&u, Ui) * store_u256(&v, 0) *
		    store_u256(&r, R3) * store_u256(&s, Si) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ in_place
		 */
	}
	/*@ Assert
	  exists R4n,
	    a == a@pre && result == result@pre && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    sm2p_mont_inv_post_loop_norm(A_non_alias, R4n, k) &&
	    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
	    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
	    store_u256(&r, R4n) * store_u256(&s, Sn) *
	    UndefStructPredu32(&t) * store_sm2_rhop
	    $ non_alias
	 */
	/*@ Assert
	  exists R4i,
	    a == a@pre && result == result@pre && result == a && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    sm2p_mont_inv_post_loop_norm(A_in_place, R4i, k) &&
	    store_fp(a, A_in_place) * store_sm2_p *
	    store_u256(&u, Ui) * store_u256(&v, 0) *
	    store_u256(&r, R4i) * store_u256(&s, Si) *
	    UndefStructPredu32(&t) * store_sm2_rhop
	    $ in_place
	 */
	/*@ Given R4n $ non_alias */
	/*@ Given R4i $ in_place */
	/*@ do open_sm2_p */
	/*@ do open_store_u256 */
	u32_sub(&SM2_P, &r, &r)
	/*@
	  where (r_eq_b) A = SM2_P_Z, B = R4n
	    $ non_alias
	  where (r_eq_b) A = SM2_P_Z, B = R4i
	    $ in_place
	 */;   // r = N - r
	/*@ Assert
	  exists R5n,
	    a == a@pre && result == result@pre && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    0 <= R5n && R5n < SM2_P_Z &&
	    sm2p_mont_inv_phase1_result(A_non_alias, R5n, k) &&
	    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
	    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
	    store_u256(&r, R5n) * store_u256(&s, Sn) *
	    UndefStructPredu32(&t) * store_sm2_rhop
	    $ non_alias
	 */
	/*@ Assert
	  exists R5i,
	    a == a@pre && result == result@pre && result == a && i == 0 &&
	    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
	    0 <= R5i && R5i < SM2_P_Z &&
	    sm2p_mont_inv_phase1_result(A_in_place, R5i, k) &&
	    store_fp(a, A_in_place) * store_sm2_p *
	    store_u256(&u, Ui) * store_u256(&v, 0) *
	    store_u256(&r, R5i) * store_u256(&s, Si) *
	    UndefStructPredu32(&t) * store_sm2_rhop
	    $ in_place
	 */
	/*@ Given R5n $ non_alias */
	/*@ Given R5i $ in_place */

	// r = a^(-1) * 2^(k)    //  256 <= k <= 512

	// Phase II  ->
	if (k != 256)
	{
		/*@ Assert
		  exists K0n,
		    a == a@pre && result == result@pre && i == 0 &&
		    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
		    K0n == k && K0n != 256 && 0 <= R5n && R5n < SM2_P_Z &&
		    sm2p_mont_inv_phase1_result(A_non_alias, R5n, K0n) &&
		    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
		    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		    store_u256(&r, R5n) * store_u256(&s, Sn) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ non_alias
		 */
		/*@ Assert
		  exists K0i,
		    a == a@pre && result == result@pre && result == a && i == 0 &&
		    0 <= carry && carry <= 1 && 256 <= k && k <= 512 &&
		    K0i == k && K0i != 256 && 0 <= R5i && R5i < SM2_P_Z &&
		    sm2p_mont_inv_phase1_result(A_in_place, R5i, K0i) &&
		    store_fp(a, A_in_place) * store_sm2_p *
		    store_u256(&u, Ui) * store_u256(&v, 0) *
		    store_u256(&r, R5i) * store_u256(&s, Si) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ in_place
		 */
		/*@ Given K0n $ non_alias */
		/*@ Given K0i $ in_place */
		memset(&t, 0, 32);
		k = 2 * 256 - k;  // k = 2m - k
		i = k / 64;
		k = k % 64;
		/*@ Assert
		  a == a@pre && result == result@pre &&
		  0 <= carry && carry <= 1 &&
		  0 <= i && i < 4 && 0 <= k && k < 64 &&
		  sm2p_mont_inv_phase1_result(A_non_alias, R5n, K0n) &&
		  sm2p_mont_inv_phase2_index(K0n, i, k) &&
		  store_fp(a, A_non_alias) * UndefStructPredu32(result) *
		  store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		  store_u256(&r, R5n) * store_u256(&s, Sn) *
		  UInt64Array::full(&(t.v[0]), 4,
		    cons(0, cons(0, cons(0, cons(0, nil))))) *
		  store_sm2_rhop
		  $ non_alias
		 */
		/*@ Assert
		  a == a@pre && result == result@pre && result == a &&
		  0 <= carry && carry <= 1 &&
		  0 <= i && i < 4 && 0 <= k && k < 64 &&
		  sm2p_mont_inv_phase1_result(A_in_place, R5i, K0i) &&
		  sm2p_mont_inv_phase2_index(K0i, i, k) &&
		  store_fp(a, A_in_place) * store_sm2_p *
		  store_u256(&u, Ui) * store_u256(&v, 0) *
		  store_u256(&r, R5i) * store_u256(&s, Si) *
		  UInt64Array::full(&(t.v[0]), 4,
		    cons(0, cons(0, cons(0, cons(0, nil))))) *
		  store_sm2_rhop
		  $ in_place
		 */
		t.v[i] = ((UINT64)1) << k;  // t = 2^(2*m-k)

		/*@ Assert
		  exists Tn,
		    a == a@pre && result == result@pre &&
		    0 <= carry && carry <= 1 &&
		    0 <= i && i < 4 && 0 <= k && k < 64 &&
		    0 <= Tn && Tn < SM2_P_Z &&
		    sm2p_mont_inv_phase1_result(A_non_alias, R5n, K0n) &&
		    sm2p_mont_inv_phase2_index(K0n, i, k) &&
		    Tn == Z::pow(2, 512 - K0n) &&
		    store_fp(a, A_non_alias) * UndefStructPredu32(result) *
		    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		    store_u256(&r, R5n) * store_u256(&s, Sn) *
		    store_u256(&t, Tn) * store_sm2_rhop
		    $ non_alias
		 */
		/*@ Assert
		  exists Ti,
		    a == a@pre && result == result@pre && result == a &&
		    0 <= carry && carry <= 1 &&
		    0 <= i && i < 4 && 0 <= k && k < 64 &&
		    0 <= Ti && Ti < SM2_P_Z &&
		    sm2p_mont_inv_phase1_result(A_in_place, R5i, K0i) &&
		    sm2p_mont_inv_phase2_index(K0i, i, k) &&
		    Ti == Z::pow(2, 512 - K0i) &&
		    store_fp(a, A_in_place) * store_sm2_p *
		    store_u256(&u, Ui) * store_u256(&v, 0) *
		    store_u256(&r, R5i) * store_u256(&s, Si) *
		    store_u256(&t, Ti) * store_sm2_rhop
		    $ in_place
		 */
		/*@ Given Tn $ non_alias */
		/*@ Given Ti $ in_place */
		// result = r * t * 2^(-256)
		montg_mul_mod_p(&r, &t, result)
		/*@
		  where (non_alias) X = R5n, Y = Tn
		    $ non_alias
		  where (non_alias) X = R5i, Y = Ti
		    $ in_place
		 */;
		/*@ Assert
		  exists Out Kmul Kout,
		    a == a@pre && result == result@pre &&
			    0 <= carry && carry <= 1 &&
			    0 <= i && i < 4 && 0 <= k && k < 64 &&
			    0 <= Out && Out < SM2_P_Z &&
			    Out * U256_MOD == R5n * Tn + Kmul * SM2_P_Z &&
			    A_non_alias * Out == U256_MOD + Kout * SM2_P_Z &&
			    store_fp(a, A_non_alias) * store_fp(result, Out) *
		    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		    store_u256(&r, R5n) * store_u256(&s, Sn) *
		    store_u256(&t, Tn) * store_sm2_rhop
		    $ non_alias
		 */
		/*@ Assert
		  exists Out Kmul Kout,
		    a == a@pre && result == result@pre && result == a &&
			    0 <= carry && carry <= 1 &&
			    0 <= i && i < 4 && 0 <= k && k < 64 &&
			    0 <= Out && Out < SM2_P_Z &&
			    Out * U256_MOD == R5i * Ti + Kmul * SM2_P_Z &&
			    A_in_place * Out == U256_MOD + Kout * SM2_P_Z &&
			    store_fp(result, Out) *
		    store_sm2_p * store_u256(&u, Ui) * store_u256(&v, 0) *
		    store_u256(&r, R5i) * store_u256(&s, Si) *
		    store_u256(&t, Ti) * store_sm2_rhop
		    $ in_place
		 */
	}
	else
	{
		// No need to do more
		/*@ Assert
		  a == a@pre && result == result@pre && k == 256 &&
			  0 <= carry && carry <= 1 && i == 0 &&
			  0 <= R5n && R5n < SM2_P_Z &&
			  sm2p_mont_inv_phase1_result(A_non_alias, R5n, 256) &&
			  store_fp(a, A_non_alias) * UndefStructPredu32(result) *
		  store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		  store_u256(&r, R5n) * store_u256(&s, Sn) *
		  UndefStructPredu32(&t) * store_sm2_rhop
		  $ non_alias
		 */
		/*@ Assert
		  a == a@pre && result == result@pre && result == a && k == 256 &&
			  0 <= carry && carry <= 1 && i == 0 &&
			  0 <= R5i && R5i < SM2_P_Z &&
			  sm2p_mont_inv_phase1_result(A_in_place, R5i, 256) &&
			  UndefStructPredu32(result) * store_sm2_p *
		  store_u256(&u, Ui) * store_u256(&v, 0) *
		  store_u256(&r, R5i) * store_u256(&s, Si) *
		  UndefStructPredu32(&t) * store_sm2_rhop
		  $ in_place
		 */
		memcpy(result, &r, 32)
		/*@
		  where (from_u256) X = R5n
		    $ non_alias
		  where (from_u256) X = R5i
		    $ in_place
		 */;
		/*@ Assert
		  exists Kout,
		    a == a@pre && result == result@pre && k == 256 &&
			    0 <= carry && carry <= 1 && i == 0 &&
			    0 <= R5n && R5n < SM2_P_Z &&
			    A_non_alias * R5n == U256_MOD + Kout * SM2_P_Z &&
			    store_fp(a, A_non_alias) * store_fp(result, R5n) *
		    store_sm2_p * store_u256(&u, Un) * store_u256(&v, 0) *
		    store_u256(&r, R5n) * store_u256(&s, Sn) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ non_alias
		 */
		/*@ Assert
		  exists Kout,
		    a == a@pre && result == result@pre && result == a && k == 256 &&
			    0 <= carry && carry <= 1 && i == 0 &&
			    0 <= R5i && R5i < SM2_P_Z &&
			    A_in_place * R5i == U256_MOD + Kout * SM2_P_Z &&
			    store_fp(result, R5i) *
		    store_sm2_p * store_u256(&u, Ui) * store_u256(&v, 0) *
		    store_u256(&r, R5i) * store_u256(&s, Si) *
		    UndefStructPredu32(&t) * store_sm2_rhop
		    $ in_place
		 */
	}
	// result = a^(-1) * 2^(256)
	/*@ Assert
	  exists Out Kout,
	    a == a@pre && result == result@pre &&
	    0 <= carry && carry <= 1 &&
	    0 <= i && i < 4 && 0 <= k && k <= 256 &&
	    0 <= Out && Out < SM2_P_Z &&
	    A_non_alias * Out == U256_MOD + Kout * SM2_P_Z &&
	    store_fp(a, A_non_alias) * store_fp(result, Out) *
	    store_sm2_p *
	    UndefStructPredu32(&u) * UndefStructPredu32(&v) *
	    UndefStructPredu32(&r) * UndefStructPredu32(&s) *
	    UndefStructPredu32(&t) *
	    store_sm2_rhop
	    $ non_alias
	 */
	/*@ Assert
	  exists Out Kout,
	    a == a@pre && result == result@pre && result == a &&
	    0 <= carry && carry <= 1 &&
	    0 <= i && i < 4 && 0 <= k && k <= 256 &&
	    0 <= Out && Out < SM2_P_Z &&
	    A_in_place * Out == U256_MOD + Kout * SM2_P_Z &&
	    store_fp(result, Out) *
	    store_sm2_p *
	    UndefStructPredu32(&u) * UndefStructPredu32(&v) *
	    UndefStructPredu32(&r) * UndefStructPredu32(&s) *
	    UndefStructPredu32(&t) *
	    store_sm2_rhop
	    $ in_place
	 */
}
