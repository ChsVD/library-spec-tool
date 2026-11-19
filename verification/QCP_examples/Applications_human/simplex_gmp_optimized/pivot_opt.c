#include "gmp/fme/fme_def.h"

typedef unsigned int size_t;
#define SIZE_MAX 4294967295U

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.pivot_opt_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.normalize_opt_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.violated_fme_model_selection_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.pivot_fme_model_lib */
/*@ Extern Coq
      (simplex_dimensions_ok : Z -> Z -> Prop)
      (simplex_mpz_layout : Prop)
      (selection_basis : Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_nonbasic_columns : Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_coef : list Z -> Z -> Z -> Z -> Z)
      (pivot_two_missing : Z -> Z -> Z -> Z -> list Z -> Assertion)
      (pivot_divides_exactly : Z -> Z -> Prop)
      (pivot_basic : Z -> Z -> list Z -> list Z)
      (pivot_row_map : Z -> Z -> list Z -> list Z -> list Z)
      (normalize_columns : Z -> list Z -> list Z -> list Z -> Prop)
      (normalize_basic_zero : Z -> Z -> list Z -> list Z -> Prop)
      (normalize_result : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_optimized_result : Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_negated_slots : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_raw_table : Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_normalized_prefix : Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_elimination_slots : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (pivot_elimination_raw : Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (MpzArray::full : Z -> Z -> list Z -> Assertion)
      (MpzArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
*/

void mpz_init(mpz_ptr x)
/*@ abs
    Require undef_data_at(&(x->_mp_alloc)) *
            undef_data_at(&(x->_mp_size)) * undef_data_at(&(x->_mp_d))
    Ensure store_Z(x, 0)
*/;

void mpz_clear(mpz_ptr r)
/*@ With n
    Require store_Z(r, n)
    Ensure exists size cap ptr, r->_mp_size == size && r->_mp_alloc == cap && r->_mp_d == ptr
*/;

void mpz_abs(mpz_ptr rop, mpz_srcptr op)
/*@ neq
    With old z
    Require store_Z(rop, old) * store_Z(op, z)
    Ensure store_Z(rop, Zabs(z)) * store_Z(op, z)
*/;

void mpz_neg(mpz_ptr rop, mpz_srcptr op)
/*@ neq
    With old z
    Require store_Z(rop, old) * store_Z(op, z)
    Ensure store_Z(rop, -z) * store_Z(op, z)
*/;

void mpz_set(mpz_ptr rop, mpz_srcptr op)
/*@ neq
    With old z
    Require store_Z(rop, old) * store_Z(op, z)
    Ensure store_Z(rop, z) * store_Z(op, z)
*/;

void mpz_set_ui(mpz_ptr r, unsigned long x)
/*@ With old x0
    Require x == x0 && 0 <= x0 && store_Z(r, old)
    Ensure store_Z(r, x0)
*/;

void mpz_gcd(mpz_ptr g, mpz_srcptr u, mpz_srcptr v)
/*@ With old zu zv
    Require store_Z(g, old) * store_Z(u, zu) * store_Z(v, zv)
    Ensure store_Z(g, Zgcd(zu, zv)) * store_Z(u, zu) * store_Z(v, zv)
*/;

void mpz_divexact(mpz_ptr q, mpz_srcptr num, mpz_srcptr den)
/*@ With old zn zd
    Require q != 0 && zd != 0 && pivot_divides_exactly(zn, zd) &&
            store_Z(q, old) * store_Z(num, zn) * store_Z(den, zd)
    Ensure store_Z(q, zn / zd) * store_Z(num, zn) * store_Z(den, zd)
*/;

void mpz_mul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@ neq
    With old z1 z2
    Require store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
    Ensure store_Z(rop, z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/;

struct table {
    size_t rows, cols;
    mpz_ptr d, c, a;
    size_t *basic, *row;
    size_t *nonbasic;
};

static void normalize(struct table *t, size_t r)
/*@ normalize_staged_row
    With M K I DP CP AP BP RP NP (D: list Z) (C: list Z) (A: list Z)
         (B: list Z) (R: list Z) (N: list Z)
    Require r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
        Zlength(N) == K-M && Zlength(A) == M*K &&
        t->rows == M && t->cols == K &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        normalize_columns(K, B, R, N) && 0 < D[I] &&
        normalize_basic_zero(K, I, A, B) &&
        MpzArray::full(DP, M, D) * MpzArray::full(CP, M, C) *
        MpzArray::full(AP, M*K, A) * UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N)
    Ensure exists (Dn: list Z) (Cn: list Z) (An: list Z),
        t->rows == M && t->cols == K &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        normalize_result(M, K, I, D, C, A, N, Dn, Cn, An) &&
        MpzArray::full(DP, M, Dn) * MpzArray::full(CP, M, Cn) *
        MpzArray::full(AP, M*K, An) * UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N)
*/;

static void combine(mpz_ptr out, mpz_srcptr m, mpz_srcptr a,
                    mpz_srcptr n, mpz_srcptr b)
/*@ non_alias
    With M A N B O
    Require store_Z(out, O) * store_Z(m, M) * store_Z(a, A) *
            store_Z(n, N) * store_Z(b, B)
    Ensure store_Z(out, M * A + N * B) * store_Z(m, M) * store_Z(a, A) *
           store_Z(n, N) * store_Z(b, B)
*/;

static void pivot(struct table *t, size_t r, size_t e)
/*@ nonzero_pivot
    With M K I E Q DP CP AP BP RP NP (D : list Z) (C : list Z) (A : list Z) (B : list Z) (R : list Z) (N : list Z)
    Require simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        MpzArray::full(DP, M, D) *
        MpzArray::full(CP, M, C) *
        MpzArray::full(AP, M*K, A) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N)
    Ensure exists (Df : list Z) (Cf : list Z) (Af : list Z) (Bf : list Z) (Rf : list Z) (Nf : list Z),
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        simplex_dimensions_ok(M, K-M) &&
        pivot_optimized_result(M, K, I, E, Q, D, C, A, B, R, N, Df, Cf, Af, Bf, Rf, Nf) &&
        MpzArray::full(DP, M, Df) *
        MpzArray::full(CP, M, Cf) *
        MpzArray::full(AP, M*K, Af) *
        UIntArray::full(BP, M, Bf) *
        UIntArray::full(RP, K, Rf) *
        UIntArray::full(NP, K-M, Nf)
*/

{
    size_t b = t->basic[r], k = t->cols;
    mpz_ptr a = t->a + r * k;
    /*@ Assert exists PivotSize PivotAlloc PivotLimbs,
        (a+e)->_mp_size == PivotSize &&
        (a+e)->_mp_alloc == PivotAlloc &&
        (a+e)->_mp_d == PivotLimbs &&
        Zabs(PivotSize) <= PivotAlloc &&
        same_sign(pivot_coef(A, K, I, E), PivotSize) &&
        (PivotSize == 0 => pivot_coef(A, K, I, E) == 0) &&
        (pivot_coef(A, K, I, E) == 0 => PivotSize == 0) &&
        (0 < PivotSize => 0 < pivot_coef(A, K, I, E)) &&
        (0 < pivot_coef(A, K, I, E) => 0 < PivotSize) &&
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        MpzArray::full(DP, M, D) *
        MpzArray::full(CP, M, C) *
        MpzArray::missing_i(AP, I*K+E, 0, M*K, A) *
        mpd_store_Z_compact(UINT_MOD, PivotLimbs, Zabs(pivot_coef(A, K, I, E)), Zabs(PivotSize)) *
        UIntArray::undef_seg(PivotLimbs, Zabs(PivotSize), PivotAlloc) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N)
    */
    int positive = a[e]._mp_size > 0;
    __mpz_struct p, g, m, n, tmp;
    mpz_init(&p);
    mpz_init(&g);
    mpz_init(&m);
    mpz_init(&n);
    mpz_init(&tmp);
    mpz_abs(&p, a + e);
    /* P*x_e = -sign(h)*C + sign(h)*D*x_b
       - sign(h)*sum_{v != e} A_v*x_v. */
    /*@ Assert exists Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        0 <= positive &&
        positive <= 1 &&
        (positive != 0 => pivot_coef(A, K, I, E) > 0) &&
        (positive == 0 => pivot_coef(A, K, I, E) < 0) &&
        positive == Pos &&
        MpzArray::full(DP, M, D) *
        MpzArray::full(CP, M, C) *
        MpzArray::full(AP, M*K, A) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, 0)
    */
    if (positive) {
        /*@ Assert
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_coef(A, K, I, E) > 0 &&
        positive == 1 &&
        MpzArray::full(DP, M, D) *
        MpzArray::missing_i(CP, I, 0, M, C) *
        store_Z(t->c+r, C[I]) *
        MpzArray::full(AP, M*K, A) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, 0)
        */
        mpz_neg(&tmp, t->c + r);
        mpz_set(t->c + r, &tmp);
        /*@ Inv Assert exists (Ac : list Z) T,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_coef(A, K, I, E) > 0 &&
        0 <= slot &&
        slot <= K-M &&
        pivot_negated_slots(M, K, I, slot, A, N, Ac) &&
        positive == 1 &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, D) *
        MpzArray::full(CP, M, replace_Znth(I, -C[I], C)) *
        MpzArray::full(AP, M*K, Ac) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
        */
        for (size_t slot = 0; slot < t->cols - t->rows; ++slot) {
            size_t v = t->nonbasic[slot];
            /*@ Assert exists (Ac : list Z) T,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_coef(A, K, I, E) > 0 &&
        0 <= slot &&
        slot <= K-M &&
        pivot_negated_slots(M, K, I, slot, A, N, Ac) &&
        slot < K-M &&
        v == N[slot] &&
        0 <= v &&
        v < K &&
        R[v] == SIZE_MAX &&
        positive == 1 &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, D) *
        MpzArray::full(CP, M, replace_Znth(I, -C[I], C)) *
        MpzArray::full(AP, M*K, Ac) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
            */
            if (t->row[v] != SIZE_MAX) continue;
            /*@ Assert exists (Ac : list Z) T,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_coef(A, K, I, E) > 0 &&
        0 <= slot &&
        slot <= K-M &&
        pivot_negated_slots(M, K, I, slot, A, N, Ac) &&
        slot < K-M &&
        v == N[slot] &&
        0 <= v &&
        v < K &&
        R[v] == SIZE_MAX &&
        0 <= I*K+v &&
        I*K+v < M*K &&
        positive == 1 &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, D) *
        MpzArray::full(CP, M, replace_Znth(I, -C[I], C)) *
        MpzArray::missing_i(AP, I*K+v, 0, M*K, Ac) *
        store_Z(a+v, A[I*K+v]) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
            */
            mpz_neg(&tmp, a + v);
            mpz_set(a + v, &tmp);
        }
        /*@ Assert exists (Ac : list Z) T,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_coef(A, K, I, E) > 0 &&
        pivot_negated_slots(M, K, I, K-M, A, N, Ac) &&
        0 <= I*K+b &&
        I*K+b < M*K &&
        positive == 1 &&
        Zlength(A) == M*K &&
        MpzArray::missing_i(DP, I, 0, M, D) *
        store_Z(t->d+r, D[I]) *
        MpzArray::full(CP, M, replace_Znth(I, -C[I], C)) *
        MpzArray::missing_i(AP, I*K+b, 0, M*K, Ac) *
        store_Z(a+b, Ac[I*K+b]) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
        */
        mpz_set(a + b, t->d + r);
    } else {
        /*@ Assert
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_coef(A, K, I, E) < 0 &&
        0 <= I*K+b &&
        I*K+b < M*K &&
        positive == 0 &&
        Zlength(A) == M*K &&
        MpzArray::missing_i(DP, I, 0, M, D) *
        store_Z(t->d+r, D[I]) *
        MpzArray::full(CP, M, C) *
        MpzArray::missing_i(AP, I*K+b, 0, M*K, A) *
        store_Z(a+b, A[I*K+b]) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, 0)
        */
        mpz_neg(&tmp, t->d + r);
        mpz_set(a + b, &tmp);
    }
    /*@ Assert exists (C0 : list Z) (A0 : list Z) T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_raw_table(M, K, I, E, D, C, A, B, replace_Znth(I, Zabs(pivot_coef(A, K, I, E)), D), C0, replace_Znth(I*K+E, 0, A0)) &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::missing_i(DP, I, 0, M, D) *
        store_Z(t->d+r, D[I]) *
        MpzArray::full(CP, M, C0) *
        MpzArray::missing_i(AP, I*K+E, 0, M*K, A0) *
        store_Z(a+e, A0[I*K+E]) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
    */
    mpz_set_ui(a + e, 0);
    mpz_set(t->d + r, &p);
    /* Replace exactly the entering slot; list order never controls selection. */
    /*@ Inv Assert exists (Dr : list Z) (Cr : list Z) (Ar : list Z) T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_raw_table(M, K, I, E, D, C, A, B, Dr, Cr, Ar) &&
        Zlength(Ar) == M*K &&
        0 <= slot &&
        slot <= Q &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, Dr) *
        MpzArray::full(CP, M, Cr) *
        MpzArray::full(AP, M*K, Ar) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, N) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
    */
    for (size_t slot = 0; slot < t->cols - t->rows; ++slot)
        if (t->nonbasic[slot] == e) {
            t->nonbasic[slot] = b;
            break;
        }
    /* The leaving column is now nonbasic and must participate below. */
    /*@ Assert exists (Dr : list Z) (Cr : list Z) (Ar : list Z) (Nn : list Z) T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_raw_table(M, K, I, E, D, C, A, B, Dr, Cr, Ar) &&
        Zlength(Ar) == M*K &&
        Nn == replace_Znth(Q, b, N) &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, Dr) *
        MpzArray::full(CP, M, Cr) *
        MpzArray::full(AP, M*K, Ar) *
        UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
    */
    t->basic[r] = e;
    t->row[e] = r;
    t->row[b] = SIZE_MAX;
    /*@ Assert exists (Dr : list Z) (Cr : list Z) (Ar : list Z) (Bn : list Z) (Rn : list Z) (Nn : list Z) T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        pivot_raw_table(M, K, I, E, D, C, A, B, Dr, Cr, Ar) &&
        Zlength(Ar) == M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        0 < Dr[I] &&
        normalize_basic_zero(K, I, Ar, Bn) &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, Dr) *
        MpzArray::full(CP, M, Cr) *
        MpzArray::full(AP, M*K, Ar) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
    */
    normalize(t, r);
    /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, 0, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 < Db[I] &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::missing_i(DP, I, 0, M, Db) *
        store_Z(t->d+r, Db[I]) *
        MpzArray::full(CP, M, Cb) *
        MpzArray::full(AP, M*K, Ab) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Zabs(pivot_coef(A, K, I, E))) *
        store_Z(&g, 0) *
        store_Z(&m, 0) *
        store_Z(&n, 0) *
        store_Z(&tmp, T)
    */
    mpz_set(&p, t->d + r);
    /*@ Inv Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) G Mu Nu T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, Db) *
        MpzArray::full(CP, M, Cb) *
        MpzArray::full(AP, M*K, Ab) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, G) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T)
    */
    for (size_t i = 0; i < t->rows; ++i) {
        if (i == r) continue;
        mpz_ptr ai = t->a + i * k;
        /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) G Mu Nu T Pos EnterSize EnterAlloc EnterLimbs,
        (ai+e)->_mp_size == EnterSize &&
        (ai+e)->_mp_alloc == EnterAlloc &&
        (ai+e)->_mp_d == EnterLimbs &&
        Zabs(EnterSize) <= EnterAlloc &&
        same_sign(pivot_coef(A, K, i, E), EnterSize) &&
        (EnterSize == 0 => pivot_coef(A, K, i, E) == 0) &&
        (pivot_coef(A, K, i, E) == 0 => EnterSize == 0) &&
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, Db) *
        MpzArray::full(CP, M, Cb) *
        MpzArray::missing_i(AP, i*K+E, 0, M*K, Ab) *
        mpd_store_Z_compact(UINT_MOD, EnterLimbs, Zabs(pivot_coef(A, K, i, E)), Zabs(EnterSize)) *
        UIntArray::undef_seg(EnterLimbs, Zabs(EnterSize), EnterAlloc) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, G) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T)
        */
        if (ai[e]._mp_size == 0) continue;
        mpz_gcd(&g, &p, ai + e);
        /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        0 < Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        pivot_divides_exactly(Db[I], Zgcd(Db[I], pivot_coef(A, K, i, E))) &&
        pivot_divides_exactly(pivot_coef(A, K, i, E), Zgcd(Db[I], pivot_coef(A, K, i, E))) &&
        &m != 0 &&
        &n != 0 &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, Db) *
        MpzArray::full(CP, M, Cb) *
        MpzArray::missing_i(AP, i*K+E, 0, M*K, Ab) *
        store_Z(ai+e, pivot_coef(A, K, i, E)) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T)
        */
        mpz_divexact(&m, &p, &g);
        mpz_divexact(&n, ai + e, &g);
        /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T ms mc md Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        m._mp_size == ms &&
        m._mp_alloc == mc &&
        m._mp_d == md &&
        same_sign(Mu, ms) &&
        Zabs(ms) <= mc &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::missing_i(DP, i, 0, M, Db) *
        store_Z(t->d+i, D[i]) *
        MpzArray::full(CP, M, Cb) *
        MpzArray::full(AP, M*K, Ab) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T) *
        ((ms != 1 && mpd_store_Z_compact(UINT_MOD, md, Zabs(Mu), Zabs(ms))) ||
         (ms == 1 && 1 <= Mu && Mu <= UINT_MAX && UIntArray::full(md, 1, cons(Mu, nil)))) *
        UIntArray::undef_seg(md, Zabs(ms), mc)
        */
        if (m._mp_size == 1 && m._mp_d[0] == 1)
            mpz_set(&tmp, t->d + i);
        else
        /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::missing_i(DP, i, 0, M, Db) *
        store_Z(t->d+i, D[i]) *
        MpzArray::full(CP, M, Cb) *
        MpzArray::full(AP, M*K, Ab) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T)
        */
        mpz_mul(&tmp, &m, t->d + i);
        mpz_set(t->d + i, &tmp);
        /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        positive == Pos &&
        Zlength(A) == M*K &&
        MpzArray::full(DP, M, replace_Znth(i, Mu*D[i], Db)) *
        pivot_two_missing(CP, M, i, I, Cb) *
        store_Z(t->c+i, C[i]) *
        store_Z(t->c+r, Cb[I]) *
        MpzArray::full(AP, M*K, Ab) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, Mu*D[i])
        */
        combine(&tmp, &m, t->c + i, &n, t->c + r);
        mpz_set(t->c + i, &tmp);
        /*@ Inv Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T (Ac : list Z) Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        0 <= slot &&
        slot <= K-M &&
        pivot_elimination_slots(M, K, I, E, i, slot, Mu, Nu, A, Nn, Ab, Ac) &&
        positive == Pos &&
        Zlength(A) == M*K &&
        Zlength(Ab) == M*K &&
        MpzArray::full(DP, M, replace_Znth(i, Mu*D[i], Db)) *
        MpzArray::full(CP, M, replace_Znth(i, Mu*C[i]+Nu*Cb[I], Cb)) *
        MpzArray::full(AP, M*K, Ac) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T)
        */
        for (size_t slot = 0; slot < t->cols - t->rows; ++slot) {
            size_t v = t->nonbasic[slot];
            /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T (Ac : list Z) Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        0 <= slot &&
        slot <= K-M &&
        pivot_elimination_slots(M, K, I, E, i, slot, Mu, Nu, A, Nn, Ab, Ac) &&
        slot < K-M &&
        v == Nn[slot] &&
        0 <= v &&
        v < K &&
        Rn[v] == SIZE_MAX &&
        positive == Pos &&
        Zlength(A) == M*K &&
        Zlength(Ab) == M*K &&
        MpzArray::full(DP, M, replace_Znth(i, Mu*D[i], Db)) *
        MpzArray::full(CP, M, replace_Znth(i, Mu*C[i]+Nu*Cb[I], Cb)) *
        MpzArray::full(AP, M*K, Ac) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T)
            */
            if (v == e) continue;
            if (t->row[v] != SIZE_MAX) continue;
            /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T (Ac : list Z) Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        0 <= slot &&
        slot <= K-M &&
        pivot_elimination_slots(M, K, I, E, i, slot, Mu, Nu, A, Nn, Ab, Ac) &&
        slot < K-M &&
        v == Nn[slot] &&
        0 <= v &&
        v < K &&
        Rn[v] == SIZE_MAX &&
        v != E &&
        0 <= i*K+v &&
        i*K+v < M*K &&
        0 <= I*K+v &&
        I*K+v < M*K &&
        i*K+v != I*K+v &&
        positive == Pos &&
        Zlength(A) == M*K &&
        Zlength(Ab) == M*K &&
        MpzArray::full(DP, M, replace_Znth(i, Mu*D[i], Db)) *
        MpzArray::full(CP, M, replace_Znth(i, Mu*C[i]+Nu*Cb[I], Cb)) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T) *
        pivot_two_missing(AP, M*K, i*K+v, I*K+v, Ac) *
        store_Z(ai+v, A[i*K+v]) *
        store_Z(a+v, Ab[I*K+v])
            */
            combine(&tmp, &m, ai + v, &n, a + v);
            mpz_set(ai + v, &tmp);
        }
        /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T (Ac : list Z) Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        pivot_elimination_slots(M, K, I, E, i, K-M, Mu, Nu, A, Nn, Ab, Ac) &&
        positive == Pos &&
        Zlength(A) == M*K &&
        Zlength(Ab) == M*K &&
        MpzArray::full(DP, M, replace_Znth(i, Mu*D[i], Db)) *
        MpzArray::full(CP, M, replace_Znth(i, Mu*C[i]+Nu*Cb[I], Cb)) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T) *
        MpzArray::missing_i(AP, i*K+E, 0, M*K, Ac) *
        store_Z(ai+e, pivot_coef(A, K, i, E))
        */
        mpz_set_ui(ai + e, 0);
        /*@ Assert exists (Bn : list Z) (Rn : list Z) (Nn : list Z) (Db : list Z) (Cb : list Z) (Ab : list Z) Mu Nu T (Di : list Z) (Ci : list Z) (Ai : list Z) Pos,
        simplex_dimensions_ok(M, K-M) &&
        simplex_mpz_layout &&
        0 <= I &&
        I < M &&
        0 <= E &&
        E < K &&
        selection_basis(M, K, D, A, B, R) &&
        pivot_nonbasic_columns(K, B, R, N) &&
        R[E] == SIZE_MAX &&
        pivot_coef(A, K, I, E) != 0 &&
        0 <= Q &&
        Q < K-M &&
        N[Q] == E &&
        Zlength(N) == K-M &&
        t->rows == M &&
        t->cols == K &&
        t->d == DP &&
        t->c == CP &&
        t->a == AP &&
        t->basic == BP &&
        t->row == RP &&
        t->nonbasic == NP &&
        r == I &&
        e == E &&
        t == t@pre &&
        k == K &&
        b == B[I] &&
        0 <= b &&
        b < K &&
        b != E &&
        a == ((mpz_ptr)AP) + I*K &&
        0 <= K-M &&
        K < UINT_MAX &&
        0 <= M*K &&
        M*K <= INT_MAX &&
        0 <= I*K &&
        I*K+K <= M*K &&
        Bn == pivot_basic(I, E, B) &&
        Rn == pivot_row_map(I, E, B, R) &&
        Nn == replace_Znth(Q, b, N) &&
        Zlength(Nn) == K-M &&
        pivot_nonbasic_columns(K, Bn, Rn, Nn) &&
        normalize_columns(K, Bn, Rn, Nn) &&
        pivot_normalized_prefix(M, K, I, E, i, D, C, A, B, Nn, Db, Cb, Ab) &&
        0 <= i &&
        i <= M &&
        0 < Db[I] &&
        i < M &&
        i != I &&
        ai == ((mpz_ptr)AP) + i*K &&
        0 <= i*K &&
        i*K+K <= M*K &&
        0 <= i*K+E &&
        i*K+E < M*K &&
        pivot_coef(A, K, i, E) != 0 &&
        Mu == Db[I] / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        Nu == pivot_coef(A, K, i, E) / Zgcd(Db[I], pivot_coef(A, K, i, E)) &&
        0 < Mu &&
        pivot_elimination_raw(M, K, I, E, i, Mu, Nu, D, C, A, Db, Cb, Ab, Di, Ci, Ai) &&
        0 < Di[i] &&
        Zlength(Ai) == M*K &&
        normalize_basic_zero(K, i, Ai, Bn) &&
        positive == Pos &&
        Zlength(A) == M*K &&
        Zlength(Ab) == M*K &&
        MpzArray::full(DP, M, Di) *
        MpzArray::full(CP, M, Ci) *
        MpzArray::full(AP, M*K, Ai) *
        UIntArray::full(BP, M, Bn) *
        UIntArray::full(RP, K, Rn) *
        UIntArray::full(NP, K-M, Nn) *
        store_Z(&p, Db[I]) *
        store_Z(&g, Zgcd(Db[I], pivot_coef(A, K, i, E))) *
        store_Z(&m, Mu) *
        store_Z(&n, Nu) *
        store_Z(&tmp, T)
        */
        normalize(t, i);
    }
    mpz_clear(&p);
    mpz_clear(&g);
    mpz_clear(&m);
    mpz_clear(&n);
    mpz_clear(&tmp);
}
