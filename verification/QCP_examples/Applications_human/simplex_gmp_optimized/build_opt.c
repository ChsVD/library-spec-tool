#include "gmp/fme/fme_def.h"

typedef unsigned int size_t;
#define SIZE_MAX 4294967295U

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.build_fme_model_input_revision_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib */
/*@ Extern Coq
      (build_row_snapshot :: *)
*/
/*@ Extern Coq
      (simplex_dimensions_ok : Z -> Z -> Prop)
      (simplex_mpz_layout : Prop)
      (simplex_malloc_token : Z -> Z -> Assertion)
      (simplex_mpz_dummy_seg : Z -> Z -> Z -> Z -> Assertion)
      (MpzArray::full : Z -> Z -> list Z -> Assertion)
      (build_row_at : list build_row_snapshot -> Z -> build_row_snapshot)
      (build_row_coefficients : build_row_snapshot -> Z)
      (build_row_next : build_row_snapshot -> Z)
      (build_row_entries : build_row_snapshot -> list Z)
      (MpzArray::missing_i : Z -> Z -> Z -> Z -> list Z -> Assertion)
      (build_input_segment : Z -> Z -> Z -> list build_row_snapshot -> Assertion)
      (build_matrix : list build_row_snapshot -> list Constraint)
      (simplex_initial_table : Z -> Z -> Z -> list Constraint -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (simplex_initial_equations : Z -> Z -> Z -> list Constraint -> list Z -> list Z -> list Z -> list Z -> Prop)
      (simplex_build_prefix : Z -> Z -> Z -> Z -> Z -> list Constraint -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
*/

/* ASSUMED standard allocator, using the same byte span and release identity as integers. */
void *malloc(size_t size)
/*@
  Require 0 <= size && size <= INT_MAX
  Ensure exists align4,
    0 <= __return && __return <= 4294967295 &&
    (0 < size => 0 < __return &&
      __return == 4 * align4 && __return + size - 1 <= 4294967295) &&
    simplex_malloc_token(__return, size) *
    UCharArray::undef_full(__return, size)
*/;

static mpz_ptr integers(size_t n)
/*@ all_counts
  Require 0 <= n && n <= INT_MAX && (0 < n => simplex_mpz_layout) &&
          0 <= n * sizeof(__mpz_struct) && n * sizeof(__mpz_struct) <= INT_MAX
  Ensure (0 < n => 0 < __return) &&
         simplex_malloc_token(__return, n * sizeof(__mpz_struct)) *
         simplex_mpz_dummy_seg(__return, 0, n, &mpz_dummy_limb)
*/;

void mpz_set_ui(mpz_ptr r, unsigned long x)
/*@
  With old x0
  Require x == x0 && 0 <= x0 && store_Z(r, old)
  Ensure store_Z(r, x0)
*/;

void mpz_set(mpz_ptr rop, mpz_srcptr op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, z) * store_Z(op, z)
*/;

struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};

struct table {
    size_t rows, cols;
    mpz_ptr d, c, a;
    size_t *basic, *row;
    size_t *nonbasic;
};

static struct table build(const struct InequList *head, size_t variables)
/*@ initial_table
    With (N : Z) (M : Z) (Rows : list build_row_snapshot)
    Require variables == N && M == Zlength(Rows) &&
            simplex_dimensions_ok(M, N) &&
            (0 < M => simplex_mpz_layout) &&
            build_input_segment(head, 0, N + 1, Rows)
    Ensure exists dPtr cPtr aPtr bPtr rowPtr nbPtr
                  (dVals : list Z) (cVals : list Z) (aVals : list Z)
                  (bVals : list Z) (rowVals : list Z) (nbVals : list Z),
           (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) &&
           simplex_initial_table(N, M, M + N, build_matrix(Rows), dVals, cVals, aVals, bVals, rowVals) &&
           simplex_initial_equations(N, M, M + N, build_matrix(Rows), dVals, cVals, aVals, bVals) &&
           __return.rows == M && __return.cols == M + N &&
           __return.d == dPtr && __return.c == cPtr && __return.a == aPtr &&
           __return.basic == bPtr && __return.row == rowPtr && __return.nonbasic == nbPtr &&
           build_input_segment(head, 0, N + 1, Rows) *
           simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) * MpzArray::full(dPtr, M, dVals) *
           simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) * MpzArray::full(cPtr, M, cVals) *
           simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) * MpzArray::full(aPtr, M * (M + N), aVals) *
           simplex_malloc_token(bPtr, M * sizeof(size_t)) * UIntArray::full(bPtr, M, bVals) *
           simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) * UIntArray::full(rowPtr, M + N, rowVals) *
           simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals)
*/
{
    struct table t;
    t.rows = 0;
    /*@ Inv Assert
        head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) &&
        0 <= t.rows && t.rows <= M &&
        simplex_dimensions_ok(M, N) && (0 < M => simplex_mpz_layout) &&
        undef_data_at(&(t.cols)) * undef_data_at(&(t.d)) * undef_data_at(&(t.c)) *
        undef_data_at(&(t.a)) * undef_data_at(&(t.basic)) * undef_data_at(&(t.row)) * undef_data_at(&(t.nonbasic)) *
        build_input_segment(head, q, N + 1, sublist(0, t.rows, Rows)) *
        build_input_segment(q, 0, N + 1, sublist(t.rows, M, Rows))
    */
    for (const struct InequList *q = head; q; q = q->next)
        /*@ Assert exists (seen : Z) (next : Z) (coef : Z),
            head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) &&
            seen == t.rows && 0 <= seen && seen < M && q != 0 &&
            next == build_row_next(build_row_at(Rows, seen)) &&
            coef != 0 && coef == build_row_coefficients(build_row_at(Rows, seen)) &&
            simplex_dimensions_ok(M, N) && (0 < M => simplex_mpz_layout) &&
            undef_data_at(&(t.cols)) * undef_data_at(&(t.d)) * undef_data_at(&(t.c)) *
            undef_data_at(&(t.a)) * undef_data_at(&(t.basic)) * undef_data_at(&(t.row)) * undef_data_at(&(t.nonbasic)) *
            store(&(q->next), next) * store(&(q->coef), coef) *
            MpzArray::full(coef, N + 1, build_row_entries(build_row_at(Rows, seen))) *
            build_input_segment(head, q, N + 1, sublist(0, seen, Rows)) *
            build_input_segment(next, 0, N + 1, sublist(seen + 1, M, Rows))
        */
        ++t.rows;
    t.cols = variables + t.rows;
    /*@ Assert
        head == head@pre && variables == variables@pre && variables == N &&
        M == Zlength(Rows) && t.rows == M && t.cols == M + N &&
        simplex_dimensions_ok(M, N) && (0 < M => simplex_mpz_layout) &&
        0 <= M && 0 <= N && M <= INT_MAX &&
        0 <= t.rows * t.cols && t.rows * t.cols <= INT_MAX &&
        0 <= M * sizeof(__mpz_struct) && M * sizeof(__mpz_struct) <= INT_MAX &&
        0 <= M * (M + N) * sizeof(__mpz_struct) &&
        M * (M + N) * sizeof(__mpz_struct) <= INT_MAX &&
        M * sizeof(size_t) <= INT_MAX && (M + N) * sizeof(size_t) <= INT_MAX &&
        N * sizeof(size_t) <= INT_MAX &&
        undef_data_at(&(t.d)) * undef_data_at(&(t.c)) * undef_data_at(&(t.a)) *
        undef_data_at(&(t.basic)) * undef_data_at(&(t.row)) * undef_data_at(&(t.nonbasic)) *
        build_input_segment(head, 0, N + 1, Rows)
    */
    t.d = integers(t.rows);
    t.c = integers(t.rows);
    t.a = integers(t.rows * t.cols);
    t.basic = malloc(t.rows * sizeof(*t.basic));
    t.row = malloc(t.cols * sizeof(*t.row));
    t.nonbasic = malloc(variables * sizeof(*t.nonbasic));
    /*@ Inv Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr (prefix : list Z),
        head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) &&
        t.rows == M && t.cols == M + N &&
        t.d == dPtr && t.c == cPtr && t.a == aPtr && t.basic == bPtr &&
        t.row == rowPtr && t.nonbasic == nbPtr &&
        simplex_dimensions_ok(M, N) && (0 < M => simplex_mpz_layout) &&
        0 <= v && v <= N && N < UINT_MAX &&
        (forall (j : Z), (0 <= j && j < v) => Znth(j, prefix, 0) == j) &&
        simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) *
        simplex_malloc_token(bPtr, M * sizeof(size_t)) *
        simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) *
        simplex_malloc_token(nbPtr, N * sizeof(size_t)) *
        simplex_mpz_dummy_seg(dPtr, 0, M, &mpz_dummy_limb) *
        simplex_mpz_dummy_seg(cPtr, 0, M, &mpz_dummy_limb) *
        simplex_mpz_dummy_seg(aPtr, 0, M * (M + N), &mpz_dummy_limb) *
        UIntArray::undef_full(bPtr, M) * UIntArray::undef_full(rowPtr, M + N) *
        UIntArray::seg(nbPtr, 0, v, prefix) * UIntArray::undef_seg(nbPtr, v, N) *
        build_input_segment(head, 0, N + 1, Rows)
    */
    for (size_t v = 0; v < variables; ++v)
        t.nonbasic[v] = v;
    /*@ Inv Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr (nbVals : list Z) (rowVals : list Z),
        head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) &&
        t.rows == M && t.cols == M + N &&
        t.d == dPtr && t.c == cPtr && t.a == aPtr && t.basic == bPtr && t.row == rowPtr && t.nonbasic == nbPtr &&
        simplex_dimensions_ok(M, N) &&
        (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) &&
        0 <= v && v <= M + N && M + N < UINT_MAX &&
        0 <= M && 0 <= N && M * (M + N) <= INT_MAX && (0 < M => simplex_mpz_layout) &&
        (forall (j : Z), (0 <= j && j < v) => Znth(j, rowVals, 0) == UINT_MAX) &&
        simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) *
        simplex_malloc_token(bPtr, M * sizeof(size_t)) *
        simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals) *
        simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) *
        simplex_mpz_dummy_seg(dPtr, 0, M, &mpz_dummy_limb) *
        simplex_mpz_dummy_seg(cPtr, 0, M, &mpz_dummy_limb) *
        simplex_mpz_dummy_seg(aPtr, 0, M * (M + N), &mpz_dummy_limb) *
        UIntArray::undef_full(bPtr, M) *
        UIntArray::seg(rowPtr, 0, v, rowVals) *
        UIntArray::undef_seg(rowPtr, v, M + N) *
        build_input_segment(head, 0, N + 1, Rows)
    */
    for (size_t v = 0; v < t.cols; ++v)
        t.row[v] = SIZE_MAX;
    const struct InequList *q = head;
    /*@ Inv Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr (nbVals : list Z) (dVals : list Z) (cVals : list Z) (aVals : list Z) (bVals : list Z) (rowVals : list Z),
        head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) &&
        t.rows == M && t.cols == M + N &&
        t.d == dPtr && t.c == cPtr && t.a == aPtr && t.basic == bPtr && t.row == rowPtr && t.nonbasic == nbPtr &&
        simplex_dimensions_ok(M, N) &&
        (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) &&
        0 <= r && r <= M && 0 <= N && N < UINT_MAX &&
        0 <= M && M < UINT_MAX && M + N < UINT_MAX &&
        M * (M + N) <= INT_MAX && (0 < M => simplex_mpz_layout) &&
        simplex_build_prefix(N, M + N, r, 0, r, build_matrix(Rows), dVals, cVals, aVals, bVals, rowVals) &&
        simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) *
        simplex_malloc_token(bPtr, M * sizeof(size_t)) *
        simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals) *
        simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) *
        MpzArray::full(dPtr, M, dVals) *
        MpzArray::full(cPtr, M, cVals) *
        MpzArray::full(aPtr, M * (M + N), aVals) *
        UIntArray::seg(bPtr, 0, r, bVals) *
        UIntArray::undef_seg(bPtr, r, M) *
        UIntArray::full(rowPtr, M + N, rowVals) *
        build_input_segment(head, q, N + 1, sublist(0, r, Rows)) *
        build_input_segment(q, 0, N + 1, sublist(r, M, Rows))
    */
    for (size_t r = 0; r < t.rows;) {
        /*@ Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr (nbVals : list Z) (dVals : list Z) (cVals : list Z) (aVals : list Z) (bVals : list Z) (rowVals : list Z),
            head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) && t.rows == M && t.cols == M + N &&
        t.d == dPtr && t.c == cPtr && t.a == aPtr && t.basic == bPtr && t.row == rowPtr && t.nonbasic == nbPtr &&
        simplex_dimensions_ok(M, N) &&
        (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) && 0 <= r && r <= M && 0 <= N && N < UINT_MAX &&
        0 <= M && M < UINT_MAX && M + N < UINT_MAX &&
        M * (M + N) <= INT_MAX && (0 < M => simplex_mpz_layout) && r < M &&
            q != 0 &&
        q->coef == build_row_coefficients(build_row_at(Rows, r)) &&
        q->next == build_row_next(build_row_at(Rows, r)) &&
        build_row_coefficients(build_row_at(Rows, r)) != 0 &&
            simplex_build_prefix(N, M + N, r, 0, r, build_matrix(Rows), dVals, cVals, aVals, bVals, rowVals) &&
            simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) *
        simplex_malloc_token(bPtr, M * sizeof(size_t)) *
        simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals) *
        simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) * UIntArray::seg(bPtr, 0, r, bVals) *
        UIntArray::undef_seg(bPtr, r, M) *
        UIntArray::full(rowPtr, M + N, rowVals) * build_input_segment(head, q, N + 1, sublist(0, r, Rows)) *
        build_input_segment(build_row_next(build_row_at(Rows, r)), 0, N + 1, sublist(r + 1, M, Rows)) * MpzArray::full(q->coef, N + 1, build_row_entries(build_row_at(Rows, r))) *
            MpzArray::missing_i(t.d, r, 0, M, dVals) * store_Z(t.d + r, 0) *
            MpzArray::full(cPtr, M, cVals) * MpzArray::full(aPtr, M * (M + N), aVals)
        */
        mpz_set_ui(t.d + r, 1);
        /*@ Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr (nbVals : list Z) (dVals : list Z) (cVals : list Z) (aVals : list Z) (bVals : list Z) (rowVals : list Z),
            head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) && t.rows == M && t.cols == M + N &&
        t.d == dPtr && t.c == cPtr && t.a == aPtr && t.basic == bPtr && t.row == rowPtr && t.nonbasic == nbPtr &&
        simplex_dimensions_ok(M, N) &&
        (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) && 0 <= r && r <= M && 0 <= N && N < UINT_MAX &&
        0 <= M && M < UINT_MAX && M + N < UINT_MAX &&
        M * (M + N) <= INT_MAX && (0 < M => simplex_mpz_layout) && r < M &&
            q != 0 &&
        q->coef == build_row_coefficients(build_row_at(Rows, r)) &&
        q->next == build_row_next(build_row_at(Rows, r)) &&
        build_row_coefficients(build_row_at(Rows, r)) != 0 &&
            simplex_build_prefix(N, M + N, r, 0, r, build_matrix(Rows), dVals, cVals, aVals, bVals, rowVals) &&
            simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) *
        simplex_malloc_token(bPtr, M * sizeof(size_t)) *
        simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals) *
        simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) * UIntArray::seg(bPtr, 0, r, bVals) *
        UIntArray::undef_seg(bPtr, r, M) *
        UIntArray::full(rowPtr, M + N, rowVals) * build_input_segment(head, q, N + 1, sublist(0, r, Rows)) *
        build_input_segment(build_row_next(build_row_at(Rows, r)), 0, N + 1, sublist(r + 1, M, Rows)) *
        MpzArray::missing_i(q->coef, 0, 0, N + 1, build_row_entries(build_row_at(Rows, r))) *
            MpzArray::missing_i(t.d, r, 0, M, dVals) * store_Z(t.d + r, 1) *
            MpzArray::missing_i(t.c, r, 0, M, cVals) * store_Z(t.c + r, 0) *
            MpzArray::full(aPtr, M * (M + N), aVals) *
            store_Z(q->coef, Znth(0, build_row_entries(build_row_at(Rows, r)), 0))
        */
        mpz_set(t.c + r, q->coef);
        /*@ Inv Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr (nbVals : list Z) (dVals : list Z) (cVals : list Z) (aVals : list Z) (bVals : list Z) (rowVals : list Z),
            head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) && t.rows == M && t.cols == M + N &&
        t.d == dPtr && t.c == cPtr && t.a == aPtr && t.basic == bPtr && t.row == rowPtr && t.nonbasic == nbPtr &&
        simplex_dimensions_ok(M, N) &&
        (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) && 0 <= r && r <= M && 0 <= N && N < UINT_MAX &&
        0 <= M && M < UINT_MAX && M + N < UINT_MAX &&
        M * (M + N) <= INT_MAX && (0 < M => simplex_mpz_layout) && r < M &&
            0 <= v && v <= N &&
            q != 0 &&
        q->coef == build_row_coefficients(build_row_at(Rows, r)) &&
        q->next == build_row_next(build_row_at(Rows, r)) &&
        build_row_coefficients(build_row_at(Rows, r)) != 0 &&
            simplex_build_prefix(N, M + N, r, v, r + 1, build_matrix(Rows), dVals, cVals, aVals, bVals, rowVals) &&
            simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) *
        simplex_malloc_token(bPtr, M * sizeof(size_t)) *
        simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals) *
        simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) * UIntArray::seg(bPtr, 0, r, bVals) *
        UIntArray::undef_seg(bPtr, r, M) *
        UIntArray::full(rowPtr, M + N, rowVals) * build_input_segment(head, q, N + 1, sublist(0, r, Rows)) *
        build_input_segment(build_row_next(build_row_at(Rows, r)), 0, N + 1, sublist(r + 1, M, Rows)) *
        MpzArray::full(q->coef, N + 1, build_row_entries(build_row_at(Rows, r))) *
        MpzArray::full(dPtr, M, dVals) *
        MpzArray::full(cPtr, M, cVals) *
        MpzArray::full(aPtr, M * (M + N), aVals)
        */
        for (size_t v = 0; v < variables; ++v)
            /*@ Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr (nbVals : list Z) (dVals : list Z) (cVals : list Z) (aVals : list Z) (bVals : list Z) (rowVals : list Z),
                head == head@pre && variables == variables@pre && variables == N && M == Zlength(Rows) && t.rows == M && t.cols == M + N &&
        t.d == dPtr && t.c == cPtr && t.a == aPtr && t.basic == bPtr && t.row == rowPtr && t.nonbasic == nbPtr &&
        simplex_dimensions_ok(M, N) &&
        (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) && 0 <= r && r <= M && 0 <= N && N < UINT_MAX &&
        0 <= M && M < UINT_MAX && M + N < UINT_MAX &&
        M * (M + N) <= INT_MAX && (0 < M => simplex_mpz_layout) && r < M && 0 <= v && v < N &&
                0 <= r * t.cols && r * t.cols <= INT_MAX &&
                0 <= r * (M + N) && r * (M + N) <= INT_MAX &&
                q != 0 &&
        q->coef == build_row_coefficients(build_row_at(Rows, r)) &&
        q->next == build_row_next(build_row_at(Rows, r)) &&
        build_row_coefficients(build_row_at(Rows, r)) != 0 && simplex_build_prefix(N, M + N, r, v, r + 1, build_matrix(Rows), dVals, cVals, aVals, bVals, rowVals) &&
                simplex_malloc_token(dPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(cPtr, M * sizeof(__mpz_struct)) *
        simplex_malloc_token(aPtr, M * (M + N) * sizeof(__mpz_struct)) *
        simplex_malloc_token(bPtr, M * sizeof(size_t)) *
        simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals) *
        simplex_malloc_token(rowPtr, (M + N) * sizeof(size_t)) * UIntArray::seg(bPtr, 0, r, bVals) *
        UIntArray::undef_seg(bPtr, r, M) *
        UIntArray::full(rowPtr, M + N, rowVals) * build_input_segment(head, q, N + 1, sublist(0, r, Rows)) *
        build_input_segment(build_row_next(build_row_at(Rows, r)), 0, N + 1, sublist(r + 1, M, Rows)) *
        MpzArray::missing_i(q->coef, v + 1, 0, N + 1, build_row_entries(build_row_at(Rows, r))) *
                MpzArray::full(dPtr, M, dVals) * MpzArray::full(cPtr, M, cVals) *
                MpzArray::missing_i(t.a, r * t.cols + v, 0, M * (M + N), aVals) *
                store_Z(t.a + r * t.cols + v, 0) *
                store_Z(q->coef + v + 1, Znth(v + 1, build_row_entries(build_row_at(Rows, r)), 0))
            */
            mpz_set(t.a + r * t.cols + v, q->coef + v + 1);
        t.basic[r] = variables + r;
        t.row[variables + r] = r;
        ++r;
        q = q->next;
    }
    return t;
}
