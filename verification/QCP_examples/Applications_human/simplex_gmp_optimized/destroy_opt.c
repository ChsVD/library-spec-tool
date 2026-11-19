#include "gmp/fme/fme_def.h"

typedef unsigned int size_t;
#define SIZE_MAX 4294967295U

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.destroy_opt_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib */
/*@ Extern Coq
      (simplex_dimensions_ok : Z -> Z -> Prop)
      (simplex_mpz_layout : Prop)
      (simplex_malloc_token : Z -> Z -> Assertion)
      (MpzArray::full : Z -> Z -> list Z -> Assertion)
*/

/* ASSUMED standard free with the exact allocation identity and byte span. */
void free(void *p)
/*@
  With bytes
  Require simplex_malloc_token(p, bytes) * UCharArray::undef_full(p, bytes)
  Ensure emp
*/;

static void release(mpz_ptr p, size_t n)
/*@ all_counts
  With (values : list Z)
  Require 0 <= n && n <= INT_MAX && (0 < n => simplex_mpz_layout) &&
          0 <= n * sizeof(__mpz_struct) && n * sizeof(__mpz_struct) <= INT_MAX &&
          simplex_malloc_token(p, n * sizeof(__mpz_struct)) *
          MpzArray::full(p, n, values)
  Ensure emp
*/;

struct table {
    size_t rows, cols;
    mpz_ptr d, c, a;
    size_t *basic, *row;
    size_t *nonbasic;
};

static void destroy(struct table *t)
/*@ destroy_owned_table
    With (M : Z) (N : Z) (DP : Z) (CP : Z) (AP : Z) (BP : Z) (RP : Z) (NP : Z)
         (DV : list Z) (CV : list Z) (AV : list Z)
    Require t->rows == M && t->cols == M + N &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        simplex_dimensions_ok(M, N) && (0 < M => simplex_mpz_layout) &&
        simplex_malloc_token(DP, M * sizeof(__mpz_struct)) * MpzArray::full(DP, M, DV) *
        simplex_malloc_token(CP, M * sizeof(__mpz_struct)) * MpzArray::full(CP, M, CV) *
        simplex_malloc_token(AP, M * (M + N) * sizeof(__mpz_struct)) *
        MpzArray::full(AP, M * (M + N), AV) *
        simplex_malloc_token(BP, M * sizeof(size_t)) * UCharArray::undef_full(BP, M * sizeof(size_t)) *
        simplex_malloc_token(RP, (M + N) * sizeof(size_t)) * UCharArray::undef_full(RP, (M + N) * sizeof(size_t)) *
        simplex_malloc_token(NP, N * sizeof(size_t)) * UCharArray::undef_full(NP, N * sizeof(size_t))
    Ensure t->rows == M && t->cols == M + N &&
        undef_data_at(&(t->d)) * undef_data_at(&(t->c)) * undef_data_at(&(t->a)) *
        undef_data_at(&(t->basic)) * undef_data_at(&(t->row)) * undef_data_at(&(t->nonbasic))
*/
{
    /*@ Assert
        t == t@pre &&
        t->rows == M && t->cols == M + N &&
        t->d == DP && t->c == CP && t->a == AP &&
        t->basic == BP && t->row == RP && t->nonbasic == NP &&
        0 <= M && M <= INT_MAX && 0 <= N &&
        0 <= M * (M + N) && M * (M + N) <= INT_MAX &&
        (0 < M => simplex_mpz_layout) &&
        (0 < M * (M + N) => simplex_mpz_layout) &&
        0 <= M * sizeof(__mpz_struct) && M * sizeof(__mpz_struct) <= INT_MAX &&
        0 <= M * (M + N) * sizeof(__mpz_struct) &&
        M * (M + N) * sizeof(__mpz_struct) <= INT_MAX &&
        simplex_malloc_token(DP, M * sizeof(__mpz_struct)) * MpzArray::full(DP, M, DV) *
        simplex_malloc_token(CP, M * sizeof(__mpz_struct)) * MpzArray::full(CP, M, CV) *
        simplex_malloc_token(AP, M * (M + N) * sizeof(__mpz_struct)) *
        MpzArray::full(AP, M * (M + N), AV) *
        simplex_malloc_token(BP, M * sizeof(size_t)) * UCharArray::undef_full(BP, M * sizeof(size_t)) *
        simplex_malloc_token(RP, (M + N) * sizeof(size_t)) * UCharArray::undef_full(RP, (M + N) * sizeof(size_t)) *
        simplex_malloc_token(NP, N * sizeof(size_t)) * UCharArray::undef_full(NP, N * sizeof(size_t))
    */
    release(t->d, t->rows);
    release(t->c, t->rows);
    release(t->a, t->rows * t->cols);
    free(t->basic);
    free(t->row);
    free(t->nonbasic);
}
