#ifndef SM2_SPEC_CONTRACT_H
#define SM2_SPEC_CONTRACT_H

/*
 * Canonical contracts for the SM2 verification functions.
 *
 * This file is documentation and is not compiled as C.  Function definitions
 * and caller declarations use the corresponding canonical contract below.
 */

/* ========================================================================== */
/* basicOp */
/* ========================================================================== */

/* basicOp/portable_addcarryx_u64.c */
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

/* basicOp/portable_mulx_u64.c */
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

/* basicOp/raw_mul.c */
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
;

/* basicOp/raw_pow.c */
void raw_pow(const UINT64 a[4], UINT64 result[8])
/*@ With A
    Require
      store_u256_limbs(a, A) *
      UInt64Array::undef_full(result, 8)
    Ensure
      0 <= A * A && A * A < U512_MOD &&
      store_u256_limbs(a, A) *
      store_u64_limbs(result, 8, A * A)
 */
;

/* basicOp/sm2n_mong_mul.c */
void sm2n_mong_mul(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_fn(x, X) *
      store_fn(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists R K,
        0 <= R && R < SM2_N_Z &&
        R * U256_MOD == X * Y + K * SM2_N_Z &&
        store_fn(x, X) *
        store_fn(y, Y) *
        store_fn(result, R) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_fn(x, X) *
      store_fn(y, Y) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists R K,
        0 <= R && R < SM2_N_Z &&
        R * U256_MOD == X * Y + K * SM2_N_Z &&
        result == x &&
        store_fn(result, R) *
        store_fn(y, Y) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

/* basicOp/sm2n_mong_mul_core.c */
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
;

/* basicOp/sm2p_mong_mul.c */
void sm2p_mong_mul(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_u256(x, X) *
      store_u256(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_u256(y, Y) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_u256(x, X) *
      store_u256(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == x &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_u256(y, Y) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_y
    With X Y
    Require
      result == y &&
      store_u256(x, X) *
      store_u256(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == y &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * Y + K * SM2_P_Z &&
        store_u256(x, X) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

/* basicOp/sm2p_mong_mul_core.c */
void sm2p_mong_mul_core(UINT64 interim[9], u32* result)
/*@ With T
    Require
      0 <= T && T < U512_MOD &&
      store_u64_limbs(interim, 8, T) *
      store(interim + 8, unsigned long long, 0) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == T + K * SM2_P_Z &&
        UInt64Array::full_shape(interim, 9) *
		store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

/* basicOp/sm2p_mong_pow.c */
void sm2p_mong_pow(const u32* x, u32* result)
/*@ non_alias
    With X
    Require
      store_u256(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * X + K * SM2_P_Z &&
        store_u256(x, X) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_x
    With X
    Require
      result == x &&
      store_u256(x, X) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == X * X + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

/* basicOp/u32_add.c */
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

/* basicOp/u32_eq.c */
bool u32_eq(const u32 *a, const u32 *b)
/*@ With (A B : Z)
    Require
      store_u256(a, A) *
      store_u256(b, B)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == B) ||
       (__return == 0 && A != B)) &&
      store_u256(a, A) *
      store_u256(b, B)
 */
;

/* basicOp/u32_eq_one.c */
bool u32_eq_one(const u32 *a)
/*@ With (A : Z)
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 1) ||
       (__return == 0 && A != 1)) &&
      store_u256(a, A)
 */
;

/* basicOp/u32_eq_zero.c */
bool u32_eq_zero(const u32 *a)
/*@ With (A : Z)
    Require
      store_u256(a, A)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && A == 0) ||
       (__return == 0 && A != 0)) &&
      store_u256(a, A)
 */
;

/* basicOp/u32_ge.c */
bool u32_ge(const u32 *a, const u32 *b)
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

/* basicOp/u32_gr.c */
bool u32_gr(const u32 *a, const u32 *b)
/*@ With (A B : Z)
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

/* basicOp/u32_shl.c */
u1 u32_shl(u32 *input)
/*@ With (X : Z)
    Require
      store_u256(input, X)
    Ensure
      exists Y,
      u256_shl_result(X, Y, __return) &&
      store_u256(input, Y)
 */
;

/* basicOp/u32_shr.c */
void u32_shr(u32 *input)
/*@ With (X : Z)
    Require
      store_u256(input, X)
    Ensure
      store_u256(input, X / 2)
 */
;

/* basicOp/u32_sub.c */
void u32_sub(const u32* a, const u32* b, u32* result)
/*@ non_alias
    With A B
    Require
      store_u256(a, A) *
      store_u256(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4)
    Ensure
      exists S borrow,
        0 <= S && S < U256_MOD &&
        0 <= borrow && borrow <= 1 &&
        A - B == S - borrow * U256_MOD &&
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

/* ========================================================================== */
/* fieldOp */
/* ========================================================================== */

/* fieldOp/MontgInvModn.c */
void MontgInvModn(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      A != 0 &&
      store_fn(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Z K,
        0 <= Z && Z < SM2_N_Z &&
        A * Z == U256_MOD + K * SM2_N_Z &&
        store_fn(a, A) *
        store_fn(result, Z) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ in_place
    With A
    Require
      result == a &&
      A != 0 &&
      store_fn(a, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Z K,
        result == a &&
        0 <= Z && Z < SM2_N_Z &&
        A * Z == U256_MOD + K * SM2_N_Z &&
        store_fn(result, Z) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

void MontgInvModn(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      A != 0 &&
      store_fn(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Ainv,
        0 <= Ainv && Ainv < SM2_N_Z &&
        Zmod(A * Ainv, SM2_N_Z) == 1 &&
        store_fn(a, A) *
        store_fn(result, mont_n(Ainv)) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

void MontgInvModn(const u32 *a, u32 *result)
/*@ mont_in_place <= in_place
    With A
    Require
      result == a &&
      A != 0 &&
      store_fn(a, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Ainv,
        result == a &&
        0 <= Ainv && Ainv < SM2_N_Z &&
        Zmod(A * Ainv, SM2_N_Z) == 1 &&
        store_fn(result, mont_n(Ainv)) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

/* fieldOp/MontgInvModp.c */
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

/* fieldOp/add_mod_n.c */
void add_mod_n(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fn(a, A) *
      store_fn(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n
    Ensure
      store_fn(a, A) *
      store_fn(b, B) *
      store_fn(result, Zmod(A + B, SM2_N_Z)) *
      store_sm2_n
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fn(a, A) *
      store_fn(b, B) *
      store_sm2_n
    Ensure
      result == b &&
      store_fn(a, A) *
      store_fn(result, Zmod(A + B, SM2_N_Z)) *
      store_sm2_n
 */
;

/* fieldOp/add_mod_p.c */
void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fp(a, A) *
      store_fp(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(b, B) *
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_sm2_p
 */
/*@ a_eq_b
    With A
    Require
      a == b &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      a == b &&
      store_fp(a, A) *
      store_fp(result, Zmod(A + A, SM2_P_Z)) *
      store_sm2_p
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_fp(b, B) *
      store_sm2_p
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == b &&
      store_fp(a, A) *
      store_fp(result, Zmod(A + B, SM2_P_Z)) *
      store_sm2_p
 */
;

void add_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias <= non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A + B)) *
      store_sm2_p
 */
;

/* fieldOp/div_by_2_mod_p.c */
void div_by_2_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      result != a &&
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, fp_div2(A)) *
      store_sm2_p
 */
/*@ in_place
    With A
    Require
      result == a &&
      store_fp(a, A) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, fp_div2(A)) *
      store_sm2_p
 */
;

void div_by_2_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      result != a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(fp_div2(A))) *
      store_sm2_p
 */
;

/* fieldOp/double_mod_p.c */
void double_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(2 * A, SM2_P_Z)) *
      store_sm2_p
 */
;

/* fieldOp/get_random_u32_in_mod_n.c */
void get_random_u32_in_mod_n(u32* k)
/*@ Require
      UInt64Array::undef_full(&(k->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon
    Ensure
      exists K,
        store_fn(k, K) *
        store_sm2_n *
        store_sm2_rhon
 */
;

/* fieldOp/inv_for_mul_mod_n.c */
void inv_for_mul_mod_n(const u32* input, u32* result)
/*@ non_alias
    With A
    Require
      A != 0 &&
      store_fn(input, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Ainv,
        0 <= Ainv && Ainv < SM2_N_Z &&
        Zmod(A * Ainv, SM2_N_Z) == 1 &&
        store_fn(input, A) *
        store_fn(result, Ainv) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ in_place
    With A
    Require
      result == input &&
      A != 0 &&
      store_fn(input, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Ainv,
        result == input &&
        0 <= Ainv && Ainv < SM2_N_Z &&
        Zmod(A * Ainv, SM2_N_Z) == 1 &&
        store_fn(result, Ainv) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

/* fieldOp/inv_for_mul_mod_p.c */
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
 */
/*@ in_place
    With A
    Require
      result == input &&
      A != 0 &&
      store_fp(input, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv,
        result == input &&
        0 <= Ainv && Ainv < SM2_P_Z &&
        Zmod(A * Ainv, SM2_P_Z) == 1 &&
        store_fp(result, Ainv) *
        store_sm2_p *
        store_sm2_rhop
 */
;

/* fieldOp/mod_n.c */
void mod_n(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      result != a &&
      store_u256(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n *
      store_sm2_rhon
    Ensure
      store_u256(a, A) *
      store_fn(result, Zmod(A, SM2_N_Z)) *
      store_sm2_n *
      store_sm2_rhon
 */
/*@ in_place
    With A
    Require
      result == a &&
      store_u256(a, A) *
      store_sm2_n *
      store_sm2_rhon
    Ensure
      result == a &&
      store_fn(result, Zmod(A, SM2_N_Z)) *
      store_sm2_n *
      store_sm2_rhon
 */
;

/* fieldOp/montg_back_mod_p.c */
void montg_back_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_u256(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A + K * SM2_P_Z &&
        store_u256(a, A) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ in_place
    With A
    Require
      result == a &&
      store_u256(a, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == a &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ regular_non_alias <= non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, A) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_back_mod_p(const u32 *a, u32 *result)
/*@ regular_in_place <= in_place
    With A
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == a &&
      store_fp(result, A) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* fieldOp/montg_mul_mod_p.c */
void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_u256(a, A) *
      store_u256(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * B + K * SM2_P_Z &&
        store_u256(a, A) *
        store_u256(b, B) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_u256(a, A) *
      store_u256(b, B) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == a &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * B + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_u256(b, B) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_u256(a, A) *
      store_u256(b, B) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == b &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * B + K * SM2_P_Z &&
        store_u256(a, A) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias <= non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_r_eq_a <= r_eq_a
    With A B
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == a &&
      store_fp(result, mont_p(A * B)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_mul_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_r_eq_b <= r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == b &&
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * B)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* fieldOp/montg_sqr_mod_p.c */
void montg_sqr_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_u256(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * A + K * SM2_P_Z &&
        store_u256(a, A) *
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ in_place
    With A
    Require
      result == a &&
      store_u256(a, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Zout K,
        result == a &&
        0 <= Zout && Zout < SM2_P_Z &&
        Zout * U256_MOD == A * A + K * SM2_P_Z &&
        store_fp(result, Zout) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A * A)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

void montg_sqr_mod_p(const u32 *a, u32 *result)
/*@ mont_in_place <= in_place
    With A
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == a &&
      store_fp(result, mont_p(A * A)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* fieldOp/montg_to_mod_p.c */
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

/* fieldOp/mul_by_2_mod_p.c */
void mul_by_2_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(2 * A, SM2_P_Z)) *
      store_sm2_p
 */
;

void mul_by_2_mod_p(const u32 *a, u32 *result)
/*@ mont_non_alias <= non_alias
    With A
    Require
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(2 * A)) *
      store_sm2_p
 */
;

/* fieldOp/mul_by_3_mod_p.c */
void mul_by_3_mod_p(const u32 *a, u32 *result)
/*@ non_alias
    With A
    Require
      store_fp(a, A) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(result, Zmod(3 * A, SM2_P_Z)) *
      store_sm2_p
 */
/*@ in_place
    With A
    Require
      result == a &&
      store_fp(a, A) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(3 * A, SM2_P_Z)) *
      store_sm2_p
 */
;

void mul_by_3_mod_p(const u32 *a, u32 *result)
/*@ mont_in_place <= in_place
    With A
    Require
      result == a &&
      0 <= A && A < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, mont_p(3 * A)) *
      store_sm2_p
 */
;

/* fieldOp/mul_mod_n.c */
void mul_mod_n(const u32* x, const u32* y, u32* result)
/*@ non_alias
    With X Y
    Require
      store_fn(x, X) *
      store_fn(y, Y) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_nh *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      store_fn(x, X) *
      store_fn(y, Y) *
      store_fn(result, Zmod(X * Y, SM2_N_Z)) *
      store_sm2_nh *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
 */
;

/* fieldOp/mul_mod_p.c */
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
 */
/*@ r_eq_x
    With X Y
    Require
      result == x &&
      store_fp(x, X) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == x &&
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ r_eq_y
    With X Y
    Require
      result == y &&
      store_fp(x, X) *
      store_fp(y, Y) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == y &&
      store_fp(x, X) *
      store_fp(result, Zmod(X * Y, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* fieldOp/pow_mod_p.c */
void pow_mod_p(const u32* x, u32* result)
/*@ non_alias
    With X
    Require
      store_fp(x, X) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_fp(x, X) *
      store_fp(result, Zmod(X * X, SM2_P_Z)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* fieldOp/solinas_reduce.c */
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
;

/* fieldOp/sub_mod_n.c */
void sub_mod_n(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fn(a, A) *
      store_fn(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_n
    Ensure
      store_fn(a, A) *
      store_fn(b, B) *
      store_fn(result, Zmod(A - B, SM2_N_Z)) *
      store_sm2_n
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fn(a, A) *
      store_fn(b, B) *
      store_sm2_n
    Ensure
      result == b &&
      store_fn(a, A) *
      store_fn(result, Zmod(A - B, SM2_N_Z)) *
      store_sm2_n
 */
;

/* fieldOp/sub_mod_p.c */
void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ non_alias
    With A B
    Require
      store_fp(a, A) *
      store_fp(b, B) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, A) *
      store_fp(b, B) *
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_sm2_p
 */
/*@ r_eq_a
    With A B
    Require
      result == a &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == a &&
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_fp(b, B) *
      store_sm2_p
 */
/*@ r_eq_b
    With A B
    Require
      result == b &&
      store_fp(a, A) *
      store_fp(b, B) *
      store_sm2_p
    Ensure
      result == b &&
      store_fp(a, A) *
      store_fp(result, Zmod(A - B, SM2_P_Z)) *
      store_sm2_p
 */
;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_non_alias <= non_alias
    With A B
    Require
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      UInt64Array::undef_full(&(result->v[0]), 4) *
      store_sm2_p
    Ensure
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_fp(result, mont_p(A - B)) *
      store_sm2_p
 */
;

void sub_mod_p(const u32 *a, const u32 *b, u32 *result)
/*@ mont_r_eq_b <= r_eq_b
    With A B
    Require
      result == b &&
      0 <= A && A < SM2_P_Z &&
      0 <= B && B < SM2_P_Z &&
      store_fp(a, mont_p(A)) *
      store_fp(b, mont_p(B)) *
      store_sm2_p
    Ensure
      result == b &&
      store_fp(a, mont_p(A)) *
      store_fp(result, mont_p(A - B)) *
      store_sm2_p
 */
;

/* ========================================================================== */
/* Milestone 3: ECC point representation and point operations */
/* ========================================================================== */

/*
 * The complete contracts below are the cross-group freeze candidates.
 * The remaining declarations record the required branches and result meaning.
 */

/* ecc.c::equ_to_AFPoint_one
 * Branches: single read-only input.
 * Result: true exactly for the affine infinity encoding (0, 0).
 * The point contract is derived once in the definition file.  Callers copy it
 * as an independent `point` tag rather than repeating `point <= base`.
 */
bool equ_to_AFPoint_one(const AFPoint* point)
/*@ base
    With X Y
    Require
      store_afpoint_fields(point, X, Y)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && X == 0 && Y == 0) ||
       (__return == 0 && (X != 0 || Y != 0))) &&
      store_afpoint_fields(point, X, Y)
 */
;

bool equ_to_AFPoint_one(const AFPoint* point)
/*@ point <= base
    With (P : ec_point)
    Require
      store_afpoint(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_afpoint(point, P)
 */
;

/* ecc.c::equ_to_JPoint_one
 * The point contract is derived once in the definition file.  Callers copy it
 * as an independent `point` tag rather than repeating `point <= base`.
 */
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
;

bool equ_to_JPoint_one(const JPoint* point)
/*@ point <= base
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point, P)
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_jpoint_with_canonical_infinity(point, P)
 */
;

/* ecc.c::is_on_curve
 * Branches: single read-only input.
 * Result: valid_afpoint(X, Y).
 */
bool is_on_curve(const AFPoint* point)
/*@ With X Y
    Require
      store_afpoint_fields(point, X, Y) *
      store_sm2_a *
      store_sm2_b *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && valid_afpoint(X, Y)) ||
       (__return == 0 && (! valid_afpoint(X, Y)))) &&
      store_afpoint_fields(point, X, Y) *
      store_sm2_a *
      store_sm2_b *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* ecc.c::affine_to_jacobian
 * Branches: non_alias.
 * Result: afpoint_to_jpoint_coordinates(X, Y, RX, RY, RZ).
 */
void affine_to_jacobian(const AFPoint* point, JPoint* result)
/*@ non_alias
    With X Y
    Require
      store_afpoint_fields(point, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_jpoint_zero
    Ensure
      exists RX RY RZ,
        afpoint_to_jpoint_coordinates(X, Y, RX, RY, RZ) &&
        store_afpoint_fields(point, X, Y) *
        store_jpoint_fields(result, RX, RY, RZ) *
        store_jpoint_zero
 */
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_jpoint_zero
    Ensure
      store_afpoint(point, P) *
      store_jpoint_with_canonical_infinity(result, P) *
      store_jpoint_zero
 */
;

/* ecc.c::jacobian_to_affine
 * Branches: non_alias.
 * Result: the affine representative of the input Jacobian point.
 */
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

/* ecc.c::AFPoint_neg
 * Branches: non_alias.
 * Result: (X, -Y mod SM2_P_Z).
 */
void AFPoint_neg(const AFPoint* point, AFPoint* result)
/*@ non_alias
    With X Y
    Require
      Y != 0 &&
      store_afpoint_fields(point, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p
    Ensure
      store_afpoint_fields(point, X, Y) *
      store_afpoint_fields(result, X, Zmod(-Y, SM2_P_Z)) *
      store_sm2_p
 */
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      P != ECInfinity &&
      store_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p
    Ensure
      store_afpoint(point, P) *
      store_afpoint(result, sm2_point_negate(P)) *
      store_sm2_p
 */
/*@ mont_point_non_alias <= non_alias
    With (P : ec_point)
    Require
      P != ECInfinity &&
      store_mont_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_sm2_p
    Ensure
      store_mont_afpoint(point, P) *
      store_mont_afpoint(result, sm2_point_negate(P)) *
      store_sm2_p
 */
;

/* ecc.c::add_JPoint_and_AFPoint
 * Branches: non_alias, r_eq_point1.
 * Result: the Jacobian representation of point1 + point2.
 * The finite non-identity inputs must represent different points.
 */
void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ impl_non_alias
    With (P1 P2 : ec_point)
    Require
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_mixed_add_result_impl(result, P1, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
/*@ impl_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      result == point1 &&
      store_mixed_add_result_impl(result, P1, P2) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ non_alias <= impl_non_alias
    With (P1 P2 : ec_point)
    Require
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_jpoint(result, sm2_point_add(P1, P2)) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ canonical_non_alias <= impl_non_alias
    With (P1 P2 : ec_point)
    Require
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      (P1 == ECInfinity || P2 == ECInfinity ||
       sm2_point_add(P1, P2) != ECInfinity) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_jpoint_with_canonical_infinity(
        result, sm2_point_add(P1, P2)) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ r_eq_point1 <= impl_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      result == point1 &&
      store_jpoint(result, sm2_point_add(P1, P2)) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ canonical_r_eq_point1 <= impl_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      (P1 == ECInfinity || P2 == ECInfinity ||
       sm2_point_add(P1, P2) != ECInfinity) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
    Ensure
      result == point1 &&
      store_jpoint_with_canonical_infinity(
        result, sm2_point_add(P1, P2)) *
      store_afpoint(point2, P2) *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero
 */
;

/* ecc_montg.c::montg_apoint_to_montg
 * Branches: non_alias.
 * Result: ordinary affine coordinates converted to Montgomery form.
 */
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

/* ecc_montg.c::montg_inv_mod_n_ex
 * Branches: non_alias, in_place.
 * Result: the same Montgomery inverse relation as MontgInvModn.
 */
void montg_inv_mod_n_ex(const UINT64 a[4], UINT64 r[4])
/*@ non_alias
    With A
    Require
      A != 0 && A < SM2_N_Z &&
      store_u256_limbs(a, A) *
      UInt64Array::undef_full(r, 4) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Znon K1non,
        0 <= Znon && Znon < SM2_N_Z &&
        A * Znon == U256_MOD + K1non * SM2_N_Z &&
        store_u256_limbs(a, A) *
        store_u256_limbs(r, Znon) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
/*@ in_place
    With A
    Require
      r == a &&
      A != 0 && A < SM2_N_Z &&
      store_u256_limbs(a, A) *
      store_sm2_n *
      store_sm2_rhon *
      store_sm2_neg_inv_n
    Ensure
      exists Zin K1in,
        r == a &&
        0 <= Zin && Zin < SM2_N_Z &&
        A * Zin == U256_MOD + K1in * SM2_N_Z &&
        store_u256_limbs(r, Zin) *
        store_sm2_n *
        store_sm2_rhon *
        store_sm2_neg_inv_n
 */
;

/* ecc.c::double_JPoint
 * Branches: non_alias, in_place.
 * Result: jpoint_double_coordinates(JX, JY, JZ, RX, RY, RZ).
 */
void double_JPoint(const JPoint* point, JPoint* result)
/*@ non_alias
    With (P : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point, P) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, x), u32, v), 4) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, y), u32, v), 4) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, z), u32, v), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_jpoint_with_canonical_infinity(point, P) *
      store_jpoint_with_canonical_infinity(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ in_place
    With (P : ec_point)
    Require
      result == point &&
      store_jpoint_with_canonical_infinity(point, P) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == point &&
      store_jpoint_with_canonical_infinity(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* ecc.c::add_JPoint
 * Branches: non_alias, r_eq_point1.
 * Result: the Jacobian representation of point1 + point2.
 */
void add_JPoint(
    const JPoint* point1, const JPoint* point2, JPoint* result)
/*@ non_alias
    With (P1 P2 : ec_point)
    Require
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_jpoint_with_canonical_infinity(point2, P2) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, x), u32, v), 4) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, y), u32, v), 4) *
      UInt64Array::undef_full(field_addr(field_addr(result, JPoint, z), u32, v), 4) *
      store_jpoint_zero *
      store_sm2_inv2p *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_jpoint_with_canonical_infinity(point2, P2) *
      store_jpoint_with_canonical_infinity(result, sm2_point_add(P1, P2)) *
      store_jpoint_zero *
      store_sm2_inv2p *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_jpoint_with_canonical_infinity(point2, P2) *
      store_jpoint_zero *
      store_sm2_inv2p *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == point1 &&
      store_jpoint_with_canonical_infinity(point2, P2) *
      store_jpoint_with_canonical_infinity(result, sm2_point_add(P1, P2)) *
      store_jpoint_zero *
      store_sm2_inv2p *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* ecc_montg.c::montg_double_jpoint */
void montg_double_jpoint(const JPoint* point, JPoint* result)
/*@ non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_mont_jpoint(point, P) *
      store_mont_jpoint(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ in_place
    With (P : ec_point)
    Require
      result == point &&
      store_mont_jpoint(point, P) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == point &&
      store_mont_jpoint(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* ecc_montg.c::montg_double_jpoint_ex
 * Branches: non_alias, in_place.
 * Result: the same contracts as montg_double_jpoint.
 */
void montg_double_jpoint_ex(const JPoint* point, JPoint* result)
/*@ non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      store_mont_jpoint(point, P) *
      store_mont_jpoint(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
/*@ in_place
    With (P : ec_point)
    Require
      result == point &&
      store_mont_jpoint(point, P) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      result == point &&
      store_mont_jpoint(result, sm2_point_double(P)) *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* ecc_montg.c::montg_equal_one
 * Branches: single read-only input.
 * Result: true exactly when the input is MONTG_ONE_Z.
 */
static inline bool montg_equal_one(const UINT64 value[4])
/*@ raw
    With A
    Require
      store_u256_limbs(value, A) *
      store_montg_one
    Ensure
      ((__return == 1 && A == MONTG_ONE_Z) ||
       (__return == 0 && A != MONTG_ONE_Z)) &&
      store_u256_limbs(value, A) *
      store_montg_one
 */
;

static inline bool montg_equal_one(const UINT64 value[4])
/*@ field <= raw
    With A P
    Require
      value == P &&
      0 <= A && A < SM2_P_Z &&
      store_fp(P, A) * store_montg_one
    Ensure
      value == P &&
      ((__return == 1 && A == MONTG_ONE_Z) ||
       (__return == 0 && A != MONTG_ONE_Z)) &&
      store_fp(P, A) * store_montg_one
 */
;

/* ecc_montg.c::bignum_is_equal */
static inline bool bignum_is_equal(
    const UINT64 a[4], const UINT64 b[4])
/*@ non_alias
    With A B
    Require
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B)
    Ensure
      ((__return == 1 && A == B) ||
       (__return == 0 && A != B)) &&
      store_u256_limbs(a, A) *
      store_u256_limbs(b, B)
 */
;

/* ecc_montg.c::bignum_set_to_zero
 * Branches: single output parameter.
 * Result: store_u256_limbs(value, 0).
 */
static inline void bignum_set_to_zero(UINT64 value[4])
/*@ raw
    Require
      UInt64Array::undef_full(value, 4)
    Ensure
      store_u256_limbs(value, 0)
 */
;

static inline void bignum_set_to_zero(UINT64 value[4])
/*@ field <= raw
    With P
    Require
      value == P && UInt64Array::undef_full(value, 4)
    Ensure
      value == P && store_fp(P, 0)
 */
;

/* ecc_montg.c::copy_bignum
 * Branches: non_alias.
 * Result: destination stores the source value.
 */
static inline void copy_bignum(
    const UINT64* source, UINT64* destination)
/*@ raw
    With X
    Require
      store_u256_limbs(source, X) *
      UInt64Array::undef_full(destination, 4)
    Ensure
      store_u256_limbs(source, X) *
      store_u256_limbs(destination, X)
 */
;

static inline void copy_bignum(
    const UINT64* source, UINT64* destination)
/*@ field_non_alias <= raw
    With X PS PD
    Require
      source == PS && destination == PD &&
      0 <= X && X < SM2_P_Z &&
      store_fp(PS, X) * UInt64Array::undef_full(destination, 4)
    Ensure
      source == PS && destination == PD &&
      store_fp(PS, X) * store_fp(PD, X)
 */
;

/* ecc_montg.c::montg_set_jpoint_to_zero
 * Branches: single output parameter.
 * Result: the canonical Montgomery Jacobian encoding of infinity.
 */
static inline void montg_set_jpoint_to_zero(JPoint* result)
/*@ coords
    Require
      store_montg_one *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4)
    Ensure
      store_montg_one *
      store_mont_jpoint_coords(result, 1, 1, 0)
 */
;

static inline void montg_set_jpoint_to_zero(JPoint* result)
/*@ point <= coords
    Require
      store_montg_one *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4)
    Ensure
      store_montg_one *
      store_mont_jpoint(result, ECInfinity)
 */
;

/* ecc_montg.c::montg_is_apoint_zero */
static inline bool montg_is_apoint_zero(const AFPoint* point)
/*@ coords
    With X Y
    Require
      store_mont_afpoint_coords(point, X, Y) *
      store_bn_zero
    Ensure
      ((__return == 1 && X == 0 && Y == 0) ||
       (__return == 0 && (X != 0 || Y != 0))) &&
      store_mont_afpoint_coords(point, X, Y) *
      store_bn_zero
 */
;

static inline bool montg_is_apoint_zero(const AFPoint* point)
/*@ point <= coords
    With (P : ec_point)
    Require
      store_mont_afpoint(point, P) *
      store_bn_zero
    Ensure
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_mont_afpoint(point, P) *
      store_bn_zero
 */
;

/* ecc_montg.c::montg_is_jpoint_zero */
static inline bool montg_is_jpoint_zero(const JPoint* point)
/*@ coords
    With X Y Z
    Require
      store_mont_jpoint_coords(point, X, Y, Z) *
      store_bn_zero
    Ensure
      ((__return == 1 && Z == 0) ||
       (__return == 0 && Z != 0)) &&
      store_mont_jpoint_coords(point, X, Y, Z) *
      store_bn_zero
 */
;

static inline bool montg_is_jpoint_zero(const JPoint* point)
/*@ point <= coords
    With (P : ec_point)
    Require
      store_mont_jpoint(point, P) *
      store_bn_zero
    Ensure
      ((__return == 1 && P == ECInfinity) ||
       (__return == 0 && P != ECInfinity)) &&
      store_mont_jpoint(point, P) *
      store_bn_zero
 */
;

/* ecc_montg.c::montg_jpoint_to_apoint
 * Branches: x_only.
 * Input: a valid Montgomery Jacobian point; ry is null.
 * Result: rx stores the ordinary affine x-coordinate.
 */
int montg_jpoint_to_apoint(
    const JPoint* point, UINT64* result_x, UINT64* result_y)
/*@ x_only
    With X Y Z
    Require
      result_x != 0 && result_y == 0 &&
      store_mont_jpoint_coords(point, X, Y, Z) *
      UInt64Array::undef_full(result_x, 4) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists RX,
        __return == 1 && result_y == 0 &&
        ((Z == 0 && RX == 0) ||
         (Z != 0 &&
          (exists ZI,
            0 <= ZI && ZI < SM2_P_Z &&
            Zmod(Z * ZI, SM2_P_Z) == 1 &&
            RX == Zmod(X * ZI * ZI, SM2_P_Z)))) &&
        store_mont_jpoint_coords(point, X, Y, Z) *
        store_u256_limbs(result_x, RX) *
        store_bn_zero *
        store_montg_one *
        store_sm2_p *
        store_sm2_rhop
 */
;

int montg_jpoint_to_apoint(
    const JPoint* point, UINT64* result_x, UINT64* result_y)
/*@ point_x_only <= x_only
    With (P : ec_point)
    Require
      result_x != 0 && result_y == 0 &&
      store_mont_jpoint(point, P) *
      UInt64Array::undef_full(result_x, 4) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists RX RY,
        __return == 1 && result_y == 0 &&
        afpoint_represents(RX, RY, P) &&
        store_mont_jpoint(point, P) *
        store_u256_limbs(result_x, RX) *
        store_bn_zero *
        store_montg_one *
        store_sm2_p *
        store_sm2_rhop
 */
;

/* ecc_montg.c::montg_jpoint_to_apoint2
 * Branches: non_alias.
 * Result: a Montgomery affine representation of the input point.
 */
int montg_jpoint_to_apoint2(const JPoint* point, AFPoint* result)
/*@ non_alias
    With X Y Z
    Require
      store_mont_jpoint_coords(point, X, Y, Z) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists RX RY,
        __return == 1 &&
        ((Z == 0 && RX == 0 && RY == 0) ||
         (Z == 1 && RX == X && RY == Y) ||
         (Z != 0 && Z != 1 &&
          exists ZI,
            0 <= ZI && ZI < SM2_P_Z &&
            Zmod(Z * ZI, SM2_P_Z) == 1 &&
            RX == Zmod(X * ZI * ZI, SM2_P_Z) &&
            RY == Zmod(Y * ZI * ZI * ZI, SM2_P_Z))) &&
        store_mont_jpoint_coords(point, X, Y, Z) *
        store_mont_afpoint_coords(result, RX, RY) *
        store_bn_zero *
        store_montg_one *
        store_sm2_p *
        store_sm2_rhop
 */
;

int montg_jpoint_to_apoint2(const JPoint* point, AFPoint* result)
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_mont_jpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      __return == 1 &&
      store_mont_jpoint(point, P) *
      store_mont_afpoint(result, P) *
      store_bn_zero *
      store_montg_one *
      store_sm2_p *
      store_sm2_rhop
 */
;

/* ecc_montg.c::montg_apoint_to_jpoint2 */
int montg_apoint_to_jpoint2(const AFPoint* point, JPoint* result)
/*@ non_alias
    With X Y
    Require
      store_mont_afpoint_coords(point, X, Y) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero *
      store_montg_one
    Ensure
      exists RX RY RZ,
        __return == 1 &&
        ((X == 0 && Y == 0 &&
          RX == 1 && RY == 1 && RZ == 0) ||
         ((X != 0 || Y != 0) &&
          RX == X && RY == Y && RZ == 1)) &&
        store_mont_afpoint_coords(point, X, Y) *
        store_mont_jpoint_coords(result, RX, RY, RZ) *
        store_bn_zero *
        store_montg_one
 */
;

int montg_apoint_to_jpoint2(const AFPoint* point, JPoint* result)
/*@ point_non_alias <= non_alias
    With (P : ec_point)
    Require
      store_mont_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero *
      store_montg_one
    Ensure
      __return == 1 &&
      store_mont_afpoint(point, P) *
      store_mont_jpoint(result, P) *
      store_bn_zero *
      store_montg_one
 */
;

/* ecc_montg.c::montg_inv_mod_p_ex
 * Branches: non_alias, in_place.
 * Result: the same Montgomery inverse relation as MontgInvModp.
 */
void montg_inv_mod_p_ex(const UINT64 input[4], UINT64 result[4])
/*@ non_alias
    With A
    Require
      A != 0 && A < SM2_P_Z &&
      store_u256_limbs(input, A) *
      UInt64Array::undef_full(result, 4) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv_non,
        0 <= Ainv_non && Ainv_non < SM2_P_Z &&
        Zmod(A * Ainv_non, SM2_P_Z) == 1 &&
        store_u256_limbs(input, A) *
        store_u256_limbs(result, mont_p(Ainv_non)) *
        store_sm2_p *
        store_sm2_rhop
 */
/*@ in_place
    With A
    Require
      result == input &&
      A != 0 && A < SM2_P_Z &&
      store_u256_limbs(input, A) *
      store_sm2_p *
      store_sm2_rhop
    Ensure
      exists Ainv_in,
        result == input &&
        0 <= Ainv_in && Ainv_in < SM2_P_Z &&
        Zmod(A * Ainv_in, SM2_P_Z) == 1 &&
        store_u256_limbs(result, mont_p(Ainv_in)) *
        store_sm2_p *
        store_sm2_rhop
 */
;

void montg_inv_mod_p_ex(const UINT64 input[4], UINT64 result[4])
/*@ field_non_alias <= non_alias
    With A PA PR
    Require
      input == PA && result == PR &&
      0 <= A && A != 0 && A < SM2_P_Z &&
      store_fp(PA, A) * UInt64Array::undef_full(result, 4) *
      store_sm2_p * store_sm2_rhop
    Ensure
      exists ZI,
        input == PA && result == PR &&
        0 <= ZI && ZI < SM2_P_Z &&
        Zmod(A * ZI, SM2_P_Z) == 1 &&
        store_fp(PA, A) * store_fp(PR, mont_p(ZI)) *
        store_sm2_p * store_sm2_rhop
 */
;

/* ecc.h::CopyJPoint */
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

/* ecc_montg.c::montg_add_jpoint
 * Branches: non_alias, r_eq_a, r_eq_b.
 * Result: the Montgomery Jacobian representation of a + b.
 */
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
/*@ r_eq_b
    With (P Q : ec_point)
    Require
      r == b &&
      store_mont_jpoint(a, P) * store_mont_jpoint(b, Q) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 && r == b &&
      store_mont_jpoint(a, P) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
;

/* ecc_montg.c::montg_add_jpoint_and_apoint
 * Branches: non_alias, r_eq_a.
 * Result: the Montgomery Jacobian representation of a + b.
 */
int montg_add_jpoint_and_apoint(
    const JPoint* a, const AFPoint* b, JPoint* r)
/*@ non_alias
    With (P Q : ec_point)
    Require
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 &&
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_a
    With (P Q : ec_point)
    Require
      r == a &&
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      __return == 1 && r == a &&
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_mont_afpoint(b, Q) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
 */
;

/* ecc_montg.c::montg_add_jpoint_ex
 * Branches: non_alias, r_eq_a.
 * Result: the same contracts as montg_add_jpoint.
 */
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
;

/* ecc_montg.c::montg_add_jpoint_and_apoint_ex
 * Branches: non_alias, r_eq_a.
 * Result: the same contracts as montg_add_jpoint_and_apoint.
 */
void montg_add_jpoint_and_apoint_ex(
    const JPoint* a, const AFPoint* b, JPoint* r)
/*@ non_alias
    With (P Q : ec_point)
    Require
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      UInt64Array::undef_full(&(r->x.v[0]), 4) *
      UInt64Array::undef_full(&(r->y.v[0]), 4) *
      UInt64Array::undef_full(&(r->z.v[0]), 4) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
 */
/*@ r_eq_a
    With (P Q : ec_point)
    Require
      r == a &&
      store_mont_jpoint(a, P) * store_mont_afpoint(b, Q) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      r == a &&
      store_mont_jpoint(r, sm2_point_add(P, Q)) *
      store_mont_afpoint(b, Q) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
 */
;

/* ========================================================================== */
/* Milestone 4: scalar recoding and scalar multiplication */
/* ========================================================================== */

/* ecc_basepoint_mul.c::ML_mul_basepoint
 * Branches: non_alias.
 * Result: the ordinary Jacobian representation of K * G.
 */
void ML_mul_basepoint(const u32* k, JPoint* result)
/*@ non_alias
    With K
    Require
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_base_point_table *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero *
      store_sm2_inv2p
    Ensure
      store_fn(k, K) *
      store_jpoint_with_canonical_infinity(
        result, sm2_point_mul(K, SM2_G_POINT)) *
      store_sm2_base_point_table *
      store_sm2_p *
      store_sm2_rhop *
      store_jpoint_zero *
      store_sm2_inv2p
 */
;

/* ecc.c::get_naf_w3
 * Branches: non_alias.
 * Result: 257 least-significant-first signed width-3 NAF digits for K.
 */
void get_naf_w3(const u32* pk, int8_t naf_w3[257])
/*@ non_alias
    With K
    Require
      store_fn(pk, K) *
      CharArray::undef_full(naf_w3, 257)
    Ensure
      store_fn(pk, K) *
      store_wnaf3(naf_w3, K)
 */
;

/* ecc_montg.c::montg_pre_compute_naf_w3
 * Branches: non_alias.
 * Result: PT[1] = P, PT[3] = 3P and NT[1]/NT[3] are their negations,
 * all in Montgomery representation.  Slots 0 and 2 are not accessed.
 */
void montg_pre_compute_naf_w3(
    const AFPoint* apoint, AFPoint PT[4], AFPoint NT[4])
/*@ non_alias
    With (P : ec_point)
    Require
      P != ECInfinity &&
      store_afpoint(apoint, P) *
      wnaf3_precomp_undef(PT, NT) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
    Ensure
      store_afpoint(apoint, P) *
      store_mont_wnaf3_precomp(PT, NT, P) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
 */
;

/* ecc_montg.c::montg_times_point_naf_w3
 * Branches: non_alias.
 * Input: a non-identity SM2 curve point and a scalar in [0, N).
 * Result: the Montgomery Jacobian representation of K * P.
 */
void montg_times_point_naf_w3(
    const AFPoint* P, const u32* k, JPoint* result)
/*@ non_alias
    With (Point : ec_point) (K : Z)
    Require
      Point != ECInfinity &&
      store_afpoint(P, Point) *
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
    Ensure
      store_afpoint(P, Point) *
      store_fn(k, K) *
      store_mont_jpoint(result, sm2_point_mul(K, Point)) *
      store_sm2_h *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
 */
;

/* ecc_montg.c::montg_times_base_point
 * Branches: non_alias.
 * Result: the Montgomery Jacobian representation of K * G.
 */
void montg_times_base_point(const u32* k, JPoint* result)
/*@ non_alias
    With K
    Require
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_mont_base_point_table *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
    Ensure
      store_fn(k, K) *
      store_mont_jpoint(
        result, sm2_point_mul(K, SM2_G_POINT)) *
      store_sm2_mont_base_point_table *
      store_sm2_p *
      store_sm2_rhop *
      store_bn_zero *
      store_montg_one
 */
;

/* ========================================================================== */
/* extra.c */
/* ========================================================================== */

/* extra.c::str_reverse_in_place */
void str_reverse_in_place(u1 *str, int len)
/*@ With bytes
    Require
      0 < len &&
      store_bytes(str, len, bytes)
    Ensure
      store_bytes(str, len, rev(bytes))
 */
;

/* extra.c::u1_to_u32 */
void u1_to_u32(const u1 input[32], u32 *result)
/*@ With bytes
    Require
      store_bytes(input, 32, bytes) *
      UndefStructPredu32(result)
    Ensure
      store_bytes(input, 32, bytes) *
      store_u256(result, be_u8_list_value(bytes))
 */
;

/* ========================================================================== */
/* sm2.c */
/* ========================================================================== */

/* sm2.c::sm2_get_public_key */
void sm2_get_public_key(const PrivKey *privkey, PubKey *pubkey)
/*@ With D
    Require
      store_sm2_private_key(privkey, D) *
      UndefStructPredAFPoint(pubkey) *
      store_sm2_get_public_key_globals
    Ensure
      store_sm2_private_key(privkey, D) *
      store_sm2_public_key(
        pubkey, sm2_point_mul(D, SM2_G_POINT)) *
      store_sm2_get_public_key_globals
 */
;

/* sm2.c::sm2_keypair */
void sm2_keypair(PubKey *pubkey, PrivKey *privkey)
/*@ Require
      UndefStructPredAFPoint(pubkey) *
      undef_sm2_private_key(privkey) *
      store_sm2_keypair_globals
    Ensure
      exists D,
        store_sm2_private_key(privkey, D) *
        store_sm2_public_key(
          pubkey, sm2_point_mul(D, SM2_G_POINT)) *
        store_sm2_keypair_globals
 */
;

/* sm2.c::sm2_get_id_digest */
int sm2_get_id_digest(
    u1 result[32], const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ With ID (P : ec_point)
    Require
      sm2_id_digest_output_aligned(result, id_len) &&
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, P) *
      UCharArray::undef_full(result, 32) *
      store_sm2_za_globals
    Ensure
      (id_len <= 50 && __return == 0 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, P) *
       store_sm2_za(
         result, ID, P, sm2_za_digest(ID, P)) *
       store_sm2_za_globals)
      ||
      (id_len > 50 && __return == -1 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, P) *
       UCharArray::undef_full(result, 32) *
       store_sm2_za_globals)
 */
;

/* sm2.c::sm2_get_message_digest */
int sm2_get_message_digest(
    u1 result[32], const u1 ZA[32], const u1 *msg, size_t msg_len)
/*@ With ZABytes Message
    Require
      sm2_message_input_aligned(msg, msg_len) &&
      aligned_4(result) &&
      store_bytes(ZA, 32, ZABytes) *
      store_bytes(msg, msg_len, Message) *
      UCharArray::undef_full(result, 32) *
      store_sm3_ti
    Ensure
      __return == 0 &&
      store_bytes(ZA, 32, ZABytes) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(result, 32, sm3_digest_bytes(app(ZABytes, Message))) *
      store_sm3_ti
 */
;

/* sm2.c::sm2_sign_dgst */
int sm2_sign_dgst(SM2SIG *sig, u1 dgst[32], const PrivKey *privkey)
/*@ With DigestBytes D
    Require
      store_bytes(dgst, 32, DigestBytes) *
      store_sm2_private_key(privkey, D) *
      undef_sm2_signature(sig) *
      store_sm2_sign_dgst_globals
    Ensure
      __return == 1 &&
      (exists R S,
         sm2_signature_generated(
           be_u8_list_value(DigestBytes), D, R, S) &&
         store_bytes(dgst, 32, DigestBytes) *
         store_sm2_private_key(privkey, D) *
         store_sm2_signature(sig, R, S) *
         store_sm2_sign_dgst_globals)
 */
;

/* sm2.c::sm2_sign */
int sm2_sign(
    SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len,
    const PubKey *pubkey, const PrivKey *privkey)
/*@ generated
    With Message ID D (P : ec_point)
    Require
      id_len <= 50 &&
      sm2_message_input_aligned(msg, msg_len) &&
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_private_key(privkey, D) *
      undef_sm2_signature(sig) *
      store_sm2_sign_globals
    Ensure
      __return == 1 &&
      (exists R S,
         sm2_signature_generated(
           be_u8_list_value(
             sm2_message_digest(ID, P, Message)),
           D, R, S) &&
         store_bytes(msg, msg_len, Message) *
         store_bytes(id, id_len, ID) *
         store_sm2_public_key(pubkey, P) *
         store_sm2_private_key(privkey, D) *
         store_sm2_signature(sig, R, S) *
         store_sm2_sign_globals)
 */
/*@ verifies <= generated
    With Message ID D (P : ec_point)
    Require
      id_len <= 50 &&
      sm2_message_input_aligned(msg, msg_len) &&
      valid_sm2_keypair(D, P) &&
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_private_key(privkey, D) *
      undef_sm2_signature(sig) *
      store_sm2_sign_globals
    Ensure
      __return == 1 &&
      (exists R S,
         sm2_signature_generated(
           be_u8_list_value(
             sm2_message_digest(ID, P, Message)),
           D, R, S) &&
         sm2_signature_verifies(
           be_u8_list_value(
             sm2_message_digest(ID, P, Message)),
           P, R, S) &&
         store_bytes(msg, msg_len, Message) *
         store_bytes(id, id_len, ID) *
         store_sm2_public_key(pubkey, P) *
         store_sm2_private_key(privkey, D) *
         store_sm2_signature(sig, R, S) *
         store_sm2_sign_globals)
 */
;

/* sm2.c::sm2_verify_dgst */
int sm2_verify_dgst(
    const SM2SIG *signature, const u1 dgst[32], const AFPoint *pubkey)
/*@ verifies
    With DigestBytes (P : ec_point) SigR SigS
    Require
      P != ECInfinity &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_dgst_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        sm2_signature_verifies(
          be_u8_list_value(DigestBytes), P, SigR, SigS)) ||
       (__return == 0 &&
        (! sm2_signature_verifies(
          be_u8_list_value(DigestBytes), P, SigR, SigS)))) &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_dgst_globals
 */
/*@ generated <= verifies
    With DigestBytes (P : ec_point) SigR SigS
    Require
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_dgst_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        (exists D,
           valid_sm2_keypair(D, P) &&
           sm2_signature_generated(
             be_u8_list_value(DigestBytes), D, SigR, SigS))) ||
       (__return == 0 &&
        (! (exists D,
             valid_sm2_keypair(D, P) &&
             sm2_signature_generated(
               be_u8_list_value(DigestBytes), D, SigR, SigS))))) &&
      store_sm2_signature(signature, SigR, SigS) *
      store_bytes(dgst, 32, DigestBytes) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_dgst_globals
 */
;

/* sm2.c::sm2_verify */
int sm2_verify(
    const SM2SIG *sig, const u1 *msg, size_t msg_len,
    const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ verifies
    With Message ID (P : ec_point) SigR SigS
    Require
      id_len <= 50 &&
      P != ECInfinity &&
      sm2_message_input_aligned(msg, msg_len) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        sm2_signature_verifies(
          be_u8_list_value(
            sm2_message_digest(ID, P, Message)),
          P, SigR, SigS)) ||
       (__return == 0 &&
        (! sm2_signature_verifies(
          be_u8_list_value(
            sm2_message_digest(ID, P, Message)),
          P, SigR, SigS)))) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, P) *
      store_sm2_verify_globals
 */
/*@ generated <= verifies
    With Message ID (P : ec_point) SigR SigS
    Require
      id_len <= 50 &&
      sm2_message_input_aligned(msg, msg_len) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_globals
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 &&
        (exists D,
           valid_sm2_keypair(D, P) &&
           sm2_signature_generated(
             be_u8_list_value(
               sm2_message_digest(ID, P, Message)),
             D, SigR, SigS))) ||
       (__return == 0 &&
        (! (exists D,
             valid_sm2_keypair(D, P) &&
             sm2_signature_generated(
               be_u8_list_value(
                 sm2_message_digest(ID, P, Message)),
               D, SigR, SigS))))) &&
      store_sm2_signature(sig, SigR, SigS) *
      store_bytes(msg, msg_len, Message) *
      store_bytes(id, id_len, ID) *
      store_sm2_public_key(pubkey, P) *
      store_sm2_verify_globals
 */
;

/* ========================================================================== */
/* sm3.c */
/* ========================================================================== */

/* sm3.c::sm3_compress */
void sm3_compress(u4 digest[8], const u1 *block, size_t nblocks)
/*@ With State Blocks
    Require
      sm3_compress_input_aligned(block, nblocks) &&
      store_u32_words(digest, 8, State) *
      store_bytes(block, 64 * nblocks, Blocks) *
      store_sm3_ti
    Ensure
      store_u32_words(
        digest, 8, sm3_compress_bytes(State, Blocks)) *
      store_bytes(block, 64 * nblocks, Blocks) *
      store_sm3_ti
 */
;

/* sm3.c::sm3_init */
void sm3_init(SM3_CTX *ctx)
/*@ Require
      undef_sm3_ctx(ctx)
    Ensure
      store_sm3_ctx(ctx, nil)
 */
;

/* sm3.c::sm3_update */
void sm3_update(SM3_CTX *ctx, const u1 *data, size_t data_len)
/*@ With Prefix Chunk
    Require
      Zlength(Prefix) + data_len < SM3_MAX_BYTES &&
      sm3_update_data_aligned(
        data, data_len, Zlength(sm3_tail(Prefix))) &&
      store_sm3_ctx(ctx, Prefix) *
      store_bytes(data, data_len, Chunk) *
      store_sm3_ti
    Ensure
      store_sm3_ctx(ctx, app(Prefix, Chunk)) *
      store_bytes(data, data_len, Chunk) *
      store_sm3_ti
 */
;

/* sm3.c::sm3_final */
void sm3_final(SM3_CTX *ctx, u1 digest[32])
/*@ With Message
    Require
      aligned_4(digest) &&
      store_sm3_ctx(ctx, Message) *
      UCharArray::undef_full(digest, 32) *
      store_sm3_ti
    Ensure
      sm3_ctx_full_shape(ctx) *
      store_bytes(digest, 32, sm3_digest_bytes(Message)) *
      store_sm3_ti
 */
;

/* sm3.c::sm3 */
size_t sm3(const u1 *data, size_t datalen, u1 dgst[32])
/*@ With Message
    Require
      sm3_digest_input_aligned(data, datalen) &&
      aligned_4(dgst) &&
      store_bytes(data, datalen, Message) *
      UCharArray::undef_full(dgst, 32) *
      store_sm3_ti
    Ensure
      __return == 32 &&
      store_bytes(data, datalen, Message) *
      store_bytes(dgst, 32, sm3_digest_bytes(Message)) *
      store_sm3_ti
 */
;

#endif /* SM2_SPEC_CONTRACT_H */
