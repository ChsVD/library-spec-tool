#include "gmp/fme/fme_def.h"

typedef unsigned int size_t;
#define SIZE_MAX 4294967295U

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.normalize_opt_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.pivot_fme_model_lib */
/*@ Extern Coq
      (simplex_dimensions_ok : Z -> Z -> Prop)
      (simplex_mpz_layout : Prop)
      (MpzArray::full : Z -> Z -> list Z -> Assertion)
      (MpzArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
      (pivot_divides_exactly : Z -> Z -> Prop)
      (Z::rem : Z -> Z -> Z)
      (normalize_basic_zero : Z -> Z -> list Z -> list Z -> Prop)
      (normalize_columns : Z -> list Z -> list Z -> list Z -> Prop)
      (normalize_row_values : Z -> Z -> list Z -> list Z -> list Z -> list Z)
      (normalize_prefix_gcd : Z -> Z -> list Z -> Z)
      (normalize_row_gcd : Z -> Z -> list Z -> list Z -> list Z -> list Z -> Z)
      (normalize_coeff_prefix : Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> list Z -> Prop)
      (normalize_result : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
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

void mpz_set(mpz_ptr rop, mpz_srcptr op)
/*@ neq
    With old z
    Require store_Z(rop, old) * store_Z(op, z)
    Ensure store_Z(rop, z) * store_Z(op, z)
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

void
mpz_tdiv_r(mpz_ptr r, mpz_srcptr n, mpz_srcptr d)
/*@ separated_trunc
    With old zn zd
    Require r != 0 && zd != 0 &&
            store_Z(r, old) * store_Z(n, zn) * store_Z(d, zd)
    Ensure store_Z(r, Z::rem(zn, zd)) * store_Z(n, zn) * store_Z(d, zd)
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
*/
{
    __mpz_struct g, tmp;
    mpz_init(&g);
    mpz_init(&tmp);
    __mpz_struct remainder;
    mpz_init(&remainder);
    /*@ Assert
        t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
        Zlength(N) == K-M && Zlength(A) == M*K &&
        t->rows == M && t->cols == K &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        normalize_columns(K, B, R, N) && 0 < D[I] &&
        normalize_basic_zero(K, I, A, B) &&
        MpzArray::missing_i(DP, I, 0, M, D) * store_Z(t->d + r, D[I]) * MpzArray::full(CP, M, C) *
        MpzArray::full(AP, M*K, A) *
        UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
        store_Z(&g, 0) * store_Z(&tmp, 0) * store_Z(&remainder, 0)
    */
    mpz_set(&g, t->d + r);
    /*@ Inv Assert exists G T Rem,
        t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
        t->rows == M && t->cols == K &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        normalize_columns(K, B, R, N) && 0 < D[I] &&
        normalize_basic_zero(K, I, A, B) &&
        0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K && 0 <= slot && slot <= K-M+1 &&
        0 < G && G == normalize_prefix_gcd(D[I], slot, normalize_row_values(K, I, A, C, N)) &&
        MpzArray::full(DP, M, D) * MpzArray::full(CP, M, C) *
        MpzArray::full(AP, M*K, A) *
        UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
        store_Z(&g, G) * store_Z(&tmp, T) * store_Z(&remainder, Rem)
    */
    for (size_t slot = 0; slot <= t->cols - t->rows; ++slot) {
        size_t j = slot == t->cols - t->rows ? t->cols : t->nonbasic[slot];
        /*@ Assert exists G T Rem gs gcap gd,
            t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
            t->rows == M && t->cols == K &&
            t->d == DP && t->c == CP && t->a == AP &&
            t->basic == BP && t->row == RP && t->nonbasic == NP &&
            normalize_columns(K, B, R, N) && 0 < D[I] &&
            normalize_basic_zero(K, I, A, B) &&
            0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K && 0 <= slot && slot <= K-M+1 &&
            0 < G && G == normalize_prefix_gcd(D[I], slot, normalize_row_values(K, I, A, C, N)) &&
            ((slot == K-M && j == K) ||
            (0 <= slot && slot < K-M && j == N[slot] && 0 <= j && j < K && R[j] == SIZE_MAX)) &&
            g._mp_size == gs && g._mp_alloc == gcap && g._mp_d == gd &&
            same_sign(G, gs) && Zabs(gs) <= gcap &&
            MpzArray::full(DP, M, D) * MpzArray::full(CP, M, C) *
            MpzArray::full(AP, M*K, A) *
            UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
            store_Z(&tmp, T) * store_Z(&remainder, Rem) *
            ((gs != 1 && mpd_store_Z_compact(UINT_MOD, gd, Zabs(G), Zabs(gs))) ||
            (gs == 1 && 1 <= G && G <= UINT_MAX && UIntArray::full(gd, 1, cons(G, nil)))) *
            UIntArray::undef_seg(gd, Zabs(gs), gcap)
        */
        if (g._mp_size == 1 && g._mp_d[0] == 1) break;
        if (j < t->cols && t->row[j] != SIZE_MAX) continue;
        mpz_srcptr x = j == t->cols ? t->c + r : t->a + r * t->cols + j;
        /*@ Assert exists G T Rem X,
            t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
            t->rows == M && t->cols == K &&
            t->d == DP && t->c == CP && t->a == AP &&
            t->basic == BP && t->row == RP && t->nonbasic == NP &&
            normalize_columns(K, B, R, N) && 0 < D[I] &&
            normalize_basic_zero(K, I, A, B) &&
            0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K && 0 <= slot && slot <= K-M+1 &&
            0 < G && G == normalize_prefix_gcd(D[I], slot, normalize_row_values(K, I, A, C, N)) &&
            ((slot == K-M && j == K && x == t->c + r && X == C[I] &&
            MpzArray::missing_i(CP, I, 0, M, C) * MpzArray::full(AP, M*K, A)) ||
            (0 <= slot && slot < K-M && j == N[slot] &&
            0 <= j && j < K && R[j] == SIZE_MAX &&
            x == t->a + r * t->cols + j && X == A[I*K+j] &&
            MpzArray::full(CP, M, C) * MpzArray::missing_i(AP, I*K+j, 0, M*K, A))) *
            store_Z(x, X) * MpzArray::full(DP, M, D) *
            UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) *
            UIntArray::full(NP, K-M, N) *
            store_Z(&g, G) * store_Z(&tmp, T) * store_Z(&remainder, Rem)
        */
        if (x->_mp_size == 0) continue;
        /* g>0; gcd(g,x)=gcd(g,x mod g), including negative x. */
        mpz_tdiv_r(&remainder, x, &g);
        if (remainder._mp_size == 0) continue;
        mpz_gcd(&tmp, &g, &remainder);
        mpz_set(&g, &tmp);
    }
    /*@ Assert exists G T Rem gs gcap gd,
        t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
        t->rows == M && t->cols == K &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        normalize_columns(K, B, R, N) && 0 < D[I] &&
        normalize_basic_zero(K, I, A, B) &&
        0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K &&
        0 < G && G == normalize_row_gcd(K, I, D, C, A, N) &&
        g._mp_size == gs && g._mp_alloc == gcap && g._mp_d == gd &&
        same_sign(G, gs) && Zabs(gs) <= gcap &&
        MpzArray::full(DP, M, D) * MpzArray::full(CP, M, C) *
        MpzArray::full(AP, M*K, A) *
        UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
        store_Z(&tmp, T) * store_Z(&remainder, Rem) *
        ((gs != 1 && mpd_store_Z_compact(UINT_MOD, gd, Zabs(G), Zabs(gs))) ||
        (gs == 1 && 1 <= G && G <= UINT_MAX && UIntArray::full(gd, 1, cons(G, nil)))) *
        UIntArray::undef_seg(gd, Zabs(gs), gcap)
    */
    if (!(g._mp_size == 1 && g._mp_d[0] == 1)) {
        /*@ Assert exists G T Rem,
            t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
            t->rows == M && t->cols == K &&
            t->d == DP && t->c == CP && t->a == AP &&
            t->basic == BP && t->row == RP && t->nonbasic == NP &&
            normalize_columns(K, B, R, N) && 0 < D[I] &&
            normalize_basic_zero(K, I, A, B) &&
            0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K &&
            0 < G && G == normalize_row_gcd(K, I, D, C, A, N) &&
            &tmp != 0 && pivot_divides_exactly(D[I], G) &&
            MpzArray::missing_i(DP, I, 0, M, D) * store_Z(t->d + r, D[I]) * MpzArray::full(CP, M, C) *
            MpzArray::full(AP, M*K, A) *
            UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
            store_Z(&g, G) * store_Z(&tmp, T) * store_Z(&remainder, Rem)
        */
        mpz_divexact(&tmp, t->d + r, &g);
        mpz_set(t->d + r, &tmp);
        /*@ Inv Assert exists G T Rem (Da: list Z) (Ca: list Z) (Aa: list Z),
            t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
            t->rows == M && t->cols == K &&
            t->d == DP && t->c == CP && t->a == AP &&
            t->basic == BP && t->row == RP && t->nonbasic == NP &&
            normalize_columns(K, B, R, N) && 0 < D[I] &&
            normalize_basic_zero(K, I, A, B) &&
            0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K && 0 <= slot && slot <= K-M+1 &&
            0 < G && G == normalize_row_gcd(K, I, D, C, A, N) &&
            Da == replace_Znth(I, Z::quot(D[I], G), D) &&
            ((slot <= K-M && Ca == C) ||
            (slot == K-M+1 && Ca == replace_Znth(I, Z::quot(C[I], G), C))) &&
            normalize_coeff_prefix(M, K, I, G, Z::min(slot, K-M), A, N, Aa) &&
            MpzArray::full(DP, M, Da) * MpzArray::full(CP, M, Ca) *
            MpzArray::full(AP, M*K, Aa) *
            UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
            store_Z(&g, G) * store_Z(&tmp, T) * store_Z(&remainder, Rem)
        */
        for (size_t slot = 0; slot <= t->cols - t->rows; ++slot) {
            size_t j = slot == t->cols - t->rows ? t->cols : t->nonbasic[slot];
            /*@ Assert exists G T Rem (Da: list Z) (Ca: list Z) (Aa: list Z),
                t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
                t->rows == M && t->cols == K &&
                t->d == DP && t->c == CP && t->a == AP &&
                t->basic == BP && t->row == RP && t->nonbasic == NP &&
                normalize_columns(K, B, R, N) && 0 < D[I] &&
                normalize_basic_zero(K, I, A, B) &&
                0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K && 0 <= slot && slot <= K-M+1 &&
                0 < G && G == normalize_row_gcd(K, I, D, C, A, N) &&
                Da == replace_Znth(I, Z::quot(D[I], G), D) &&
                ((slot <= K-M && Ca == C) ||
                (slot == K-M+1 && Ca == replace_Znth(I, Z::quot(C[I], G), C))) &&
                normalize_coeff_prefix(M, K, I, G, Z::min(slot, K-M), A, N, Aa) &&
                ((slot == K-M && j == K) ||
                (0 <= slot && slot < K-M && j == N[slot] && 0 <= j && j < K && R[j] == SIZE_MAX)) &&
                MpzArray::full(DP, M, Da) * MpzArray::full(CP, M, Ca) *
                MpzArray::full(AP, M*K, Aa) *
                UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
                store_Z(&g, G) * store_Z(&tmp, T) * store_Z(&remainder, Rem)
            */
            if (j < t->cols && t->row[j] != SIZE_MAX) continue;
            mpz_ptr x = j == t->cols ? t->c + r : t->a + r * t->cols + j;
            /*@ Assert exists G T Rem X (Da: list Z) (Ca: list Z) (Aa: list Z),
                t == t@pre && r == I && simplex_dimensions_ok(M, K - M) && simplex_mpz_layout && 0 <= I && I < M &&
                t->rows == M && t->cols == K &&
                t->d == DP && t->c == CP && t->a == AP &&
                t->basic == BP && t->row == RP && t->nonbasic == NP &&
                normalize_columns(K, B, R, N) && 0 < D[I] &&
                normalize_basic_zero(K, I, A, B) &&
                0 <= K-M && K < UINT_MAX && Zlength(N) == K-M && Zlength(A) == M*K && 0 <= slot && slot <= K-M+1 &&
                0 < G && G == normalize_row_gcd(K, I, D, C, A, N) &&
                Da == replace_Znth(I, Z::quot(D[I], G), D) &&
                ((slot <= K-M && Ca == C) ||
                (slot == K-M+1 && Ca == replace_Znth(I, Z::quot(C[I], G), C))) &&
                normalize_coeff_prefix(M, K, I, G, Z::min(slot, K-M), A, N, Aa) &&
                &tmp != 0 && pivot_divides_exactly(X, G) &&
                ((slot == K-M && j == K && x == t->c + r && X == Ca[I] &&
                MpzArray::missing_i(CP, I, 0, M, Ca) * MpzArray::full(AP, M*K, Aa)) ||
                (0 <= slot && slot < K-M && j == N[slot] &&
                0 <= j && j < K && R[j] == SIZE_MAX &&
                x == t->a + r * t->cols + j && X == Aa[I*K+j] &&
                MpzArray::full(CP, M, Ca) * MpzArray::missing_i(AP, I*K+j, 0, M*K, Aa))) *
                store_Z(x, X) * MpzArray::full(DP, M, Da) *
                UIntArray::full(BP, M, B) * UIntArray::full(RP, K, R) *
                UIntArray::full(NP, K-M, N) *
                store_Z(&g, G) * store_Z(&tmp, T) * store_Z(&remainder, Rem)
            */
            if (x->_mp_size == 0) continue;
            mpz_divexact(&tmp, x, &g);
            mpz_set(x, &tmp);
        }
    }
    /*@ Assert exists G T Rem (Dn: list Z) (Cn: list Z) (An: list Z),
        t == t@pre && r == I &&
        t->rows == M && t->cols == K &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        normalize_result(M, K, I, D, C, A, N, Dn, Cn, An) &&
        MpzArray::full(DP, M, Dn) * MpzArray::full(CP, M, Cn) *
        MpzArray::full(AP, M*K, An) * UIntArray::full(BP, M, B) *
        UIntArray::full(RP, K, R) * UIntArray::full(NP, K-M, N) *
        store_Z(&g, G) * store_Z(&tmp, T) * store_Z(&remainder, Rem)
    */
    mpz_clear(&remainder);
    mpz_clear(&g);
    mpz_clear(&tmp);
}
