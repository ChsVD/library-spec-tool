#include "gmp/fme/fme_def.h"

typedef unsigned int size_t;
#define SIZE_MAX 4294967295U
#define NULL 0

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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_one_sided_policy_opt_lib */
/*@ Extern Coq
 (os_node_layout : Prop)
 (os_zeros : Z -> list Z)
 (os_coef : build_row_snapshot -> Z -> Z)
 (os_mask : Z -> list build_row_snapshot -> Z)
 (os_kept : Z -> list build_row_snapshot -> list build_row_snapshot)
 (os_kept_prefix : Z -> Z -> list build_row_snapshot -> list build_row_snapshot)
 (os_shadows : Z -> Z -> list build_row_snapshot -> list build_row_snapshot)
 (os_links : Z -> Z -> list build_row_snapshot -> Assertion)
 (os_unborrowed_kept : Z -> Z -> list build_row_snapshot -> Assertion)
 (os_size_relation : Z -> Z -> Prop)
 (os_masks_at : Z -> Z -> Z -> list build_row_snapshot -> list Z -> Prop)
 (os_checked_prefix : list build_row_snapshot -> build_row_snapshot -> Z -> Prop)
 (os_temp_head : Z -> Z -> Z)
 (os_mpz_without_size : Z -> Z -> Z -> Assertion)
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

/* ASSUMED standard allocation and byte-zeroing. */
void *calloc(size_t count, size_t bytes)
 /*@ Require bytes == 1 && 0 <= count && count <= INT_MAX
     Ensure exists align4,
       0 <= __return && __return <= 4294967295 &&
       (0 < count => 0 < __return &&
         __return == 4 * align4 && __return + count - 1 <= 4294967295) &&
       simplex_malloc_token(__return, count) *
       UCharArray::full(__return, count, os_zeros(count))
 */;
void free(void *p)
 /*@ With bytes
     Require simplex_malloc_token(p, bytes) * UCharArray::undef_full(p, bytes)
     Ensure emp
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
*/;

static struct table build_one_sided(const struct InequList *head, size_t variables)
/*@ stable_one_sided_build_normal
    With (N : Z) (M : Z) (Rows : list build_row_snapshot)
    Require variables == N && M == Zlength(Rows) &&
            simplex_dimensions_ok(M, N) &&
            (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) &&
            build_input_segment(head, 0, N + 1, Rows)
    Ensure exists dPtr cPtr aPtr bPtr rowPtr nbPtr
                  (dVals : list Z) (cVals : list Z) (aVals : list Z)
                  (bVals : list Z) (rowVals : list Z) (nbVals : list Z),
           (forall (j : Z), (0 <= j && j < N) => Znth(j, nbVals, 0) == j) &&
           simplex_initial_table(N, Zlength(os_kept(N, Rows)), Zlength(os_kept(N, Rows)) + N, build_matrix(os_kept(N, Rows)), dVals, cVals, aVals, bVals, rowVals) &&
           simplex_initial_equations(N, Zlength(os_kept(N, Rows)), Zlength(os_kept(N, Rows)) + N, build_matrix(os_kept(N, Rows)), dVals, cVals, aVals, bVals) &&
           __return.rows == Zlength(os_kept(N, Rows)) && __return.cols == Zlength(os_kept(N, Rows)) + N &&
           __return.d == dPtr && __return.c == cPtr && __return.a == aPtr &&
           __return.basic == bPtr && __return.row == rowPtr && __return.nonbasic == nbPtr &&
           build_input_segment(head, 0, N + 1, Rows) *
           simplex_malloc_token(dPtr, Zlength(os_kept(N, Rows)) * sizeof(__mpz_struct)) * MpzArray::full(dPtr, Zlength(os_kept(N, Rows)), dVals) *
           simplex_malloc_token(cPtr, Zlength(os_kept(N, Rows)) * sizeof(__mpz_struct)) * MpzArray::full(cPtr, Zlength(os_kept(N, Rows)), cVals) *
           simplex_malloc_token(aPtr, Zlength(os_kept(N, Rows)) * (Zlength(os_kept(N, Rows)) + N) * sizeof(__mpz_struct)) * MpzArray::full(aPtr, Zlength(os_kept(N, Rows)) * (Zlength(os_kept(N, Rows)) + N), aVals) *
           simplex_malloc_token(bPtr, Zlength(os_kept(N, Rows)) * sizeof(size_t)) * UIntArray::full(bPtr, Zlength(os_kept(N, Rows)), bVals) *
           simplex_malloc_token(rowPtr, (Zlength(os_kept(N, Rows)) + N) * sizeof(size_t)) * UIntArray::full(rowPtr, Zlength(os_kept(N, Rows)) + N, rowVals) *
           simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals)
*/
{
/*@ Assert head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && build_input_segment(head, 0, N + 1, Rows)
*/
    unsigned char *signs = calloc(variables, sizeof(*signs));
    size_t rows = 0;
/*@ Inv Assert exists (Masks : list Z),
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && 0 <= rows && rows <= M &&
 os_masks_at(N, rows, 0, Rows, Masks) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * build_input_segment(head, q, N + 1, sublist(0, rows, Rows)) *
 build_input_segment(q, 0, N + 1, sublist(rows, M, Rows))
*/
    for (const struct InequList *q = head; q; q = q->next) {
        ++rows;
/*@ Inv Assert exists (i : Z) (coef : Z) (next : Z) (Masks : list Z),
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && rows == i + 1 && 0 <= i && i < M &&
 q != 0 && 0 <= j && j <= N && next == build_row_next(build_row_at(Rows, i)) &&
 coef == build_row_coefficients(build_row_at(Rows, i)) && coef != 0 &&
 os_masks_at(N, i, j, Rows, Masks) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * build_input_segment(head, q, N + 1, sublist(0, i, Rows)) * store(&(q->next), next) * store(&(q->coef), coef) * MpzArray::full(coef, N + 1, build_row_entries(build_row_at(Rows, i))) * build_input_segment(next, 0, N + 1, sublist(i + 1, M, Rows))
*/
        for (size_t j = 0; j < variables; ++j) {
/*@ Assert exists (i : Z) (coef : Z) (next : Z) (sz : Z) (Masks : list Z),
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && rows == i + 1 && 0 <= i && i < M &&
 q != 0 && 0 <= j && j < N && next == build_row_next(build_row_at(Rows, i)) &&
 coef == build_row_coefficients(build_row_at(Rows, i)) && coef != 0 &&
 os_masks_at(N, i, j, Rows, Masks) &&
 os_size_relation(sz, os_coef(build_row_at(Rows, i), j)) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * build_input_segment(head, q, N + 1, sublist(0, i, Rows)) * store(&(q->next), next) * store(&(q->coef), coef) * data_at(&(((mpz_ptr)coef)[j + 1]._mp_size), int, sz) *
 os_mpz_without_size(((mpz_ptr)coef) + (j + 1), os_coef(build_row_at(Rows, i), j), sz) *
 MpzArray::missing_i(coef, j + 1, 0, N + 1, build_row_entries(build_row_at(Rows, i))) * build_input_segment(next, 0, N + 1, sublist(i + 1, M, Rows))
*/
            int sign = q->coef[j + 1]._mp_size;
            if (sign > 0) signs[j] |= 1;
            if (sign < 0) signs[j] |= 2;
        }
    }
/*@ Assert exists (Masks : list Z),
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && rows == M &&
 0 <= M * sizeof(struct InequList) && M * sizeof(struct InequList) <= INT_MAX &&
 os_masks_at(N, M, 0, Rows, Masks) && simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * build_input_segment(head, 0, N + 1, Rows)
*/
    struct InequList *nodes = malloc(rows * sizeof(*nodes));
    size_t kept = 0;
/*@ Inv Assert exists (i : Z) (NodesAlign : Z) (Masks : list Z),
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && rows == M &&
 0 <= i && i <= M && 0 <= kept && kept <= i && kept == Zlength(os_kept_prefix(N, i, Rows)) && (0 < M => 0 < nodes && nodes == 4 * NodesAlign) && 0 <= nodes && nodes <= UINT_MAX &&
 (0 < M => nodes + M * sizeof(struct InequList) - 1 <= UINT_MAX) &&
 os_masks_at(N, M, 0, Rows, Masks) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * simplex_malloc_token(nodes, M * sizeof(struct InequList)) * os_links(os_temp_head(nodes, kept), 0, os_shadows(nodes, 0, os_kept_prefix(N, i, Rows))) * UCharArray::undef_seg(nodes, kept * sizeof(struct InequList), M * sizeof(struct InequList)) * build_input_segment(head, q, N + 1, sublist(0, i, Rows)) * build_input_segment(q, 0, N + 1, sublist(i, M, Rows))
*/
    for (const struct InequList *q = head; q; q = q->next) {
        size_t j = 0;
/*@ Inv Assert exists (i : Z) (NodesAlign : Z) (coef : Z) (next : Z) (Masks : list Z),
 rows == M && 0 <= i && i < M &&
 os_masks_at(N, M, 0, Rows, Masks) &&
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && (0 < M => 0 < nodes && nodes == 4 * NodesAlign) && 0 <= nodes && nodes <= UINT_MAX &&
 (0 < M => nodes + M * sizeof(struct InequList) - 1 <= UINT_MAX) && next == build_row_next(build_row_at(Rows, i)) &&
 coef == build_row_coefficients(build_row_at(Rows, i)) && coef != 0 && 0 <= kept && kept <= i && kept == Zlength(os_kept_prefix(N, i, Rows)) && q != 0 && 0 <= j && j <= N &&
 os_checked_prefix(Rows, build_row_at(Rows, i), j) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * simplex_malloc_token(nodes, M * sizeof(struct InequList)) * os_links(os_temp_head(nodes, kept), 0, os_shadows(nodes, 0, os_kept_prefix(N, i, Rows))) * UCharArray::undef_seg(nodes, kept * sizeof(struct InequList), M * sizeof(struct InequList)) * build_input_segment(head, q, N + 1, sublist(0, i, Rows)) * store(&(q->next), next) * store(&(q->coef), coef) * MpzArray::full(coef, N + 1, build_row_entries(build_row_at(Rows, i))) * build_input_segment(next, 0, N + 1, sublist(i + 1, M, Rows))
*/
        while (j < variables) {
/*@ Assert exists (i : Z) (NodesAlign : Z) (coef : Z) (next : Z) (Masks : list Z) (sz : Z),
 rows == M && 0 <= i && i < M &&
 os_masks_at(N, M, 0, Rows, Masks) &&
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && (0 < M => 0 < nodes && nodes == 4 * NodesAlign) && 0 <= nodes && nodes <= UINT_MAX &&
 (0 < M => nodes + M * sizeof(struct InequList) - 1 <= UINT_MAX) && next == build_row_next(build_row_at(Rows, i)) &&
 coef == build_row_coefficients(build_row_at(Rows, i)) && coef != 0 && 0 <= kept && kept <= i && kept == Zlength(os_kept_prefix(N, i, Rows)) && q != 0 && 0 <= j && j < N &&
 os_checked_prefix(Rows, build_row_at(Rows, i), j) &&
 os_size_relation(sz, os_coef(build_row_at(Rows, i), j)) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * simplex_malloc_token(nodes, M * sizeof(struct InequList)) * os_links(os_temp_head(nodes, kept), 0, os_shadows(nodes, 0, os_kept_prefix(N, i, Rows))) * UCharArray::undef_seg(nodes, kept * sizeof(struct InequList), M * sizeof(struct InequList)) * build_input_segment(head, q, N + 1, sublist(0, i, Rows)) * store(&(q->next), next) * store(&(q->coef), coef) * data_at(&(((mpz_ptr)coef)[j + 1]._mp_size), int, sz) *
 os_mpz_without_size(((mpz_ptr)coef) + (j + 1), os_coef(build_row_at(Rows, i), j), sz) *
 MpzArray::missing_i(coef, j + 1, 0, N + 1, build_row_entries(build_row_at(Rows, i))) * build_input_segment(next, 0, N + 1, sublist(i + 1, M, Rows))
*/
            if ((signs[j] == 1 || signs[j] == 2) &&
                q->coef[j + 1]._mp_size != 0) break;
            ++j;
        }
        if (j != variables) continue;
/*@ Assert exists (i : Z) (NodesAlign : Z) (coef : Z) (next : Z) (Masks : list Z),
 rows == M && 0 <= i && i < M &&
 os_masks_at(N, M, 0, Rows, Masks) &&
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && (0 < M => 0 < nodes && nodes == 4 * NodesAlign) && 0 <= nodes && nodes <= UINT_MAX &&
 (0 < M => nodes + M * sizeof(struct InequList) - 1 <= UINT_MAX) && next == build_row_next(build_row_at(Rows, i)) &&
 coef == build_row_coefficients(build_row_at(Rows, i)) && coef != 0 && 0 <= kept && kept <= i && kept == Zlength(os_kept_prefix(N, i, Rows)) && q != 0 && j == N &&
 os_checked_prefix(Rows, build_row_at(Rows, i), N) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * simplex_malloc_token(nodes, M * sizeof(struct InequList)) * build_input_segment(head, q, N + 1, sublist(0, i, Rows)) * store(&(q->next), next) * store(&(q->coef), coef) * MpzArray::full(coef, N + 1, build_row_entries(build_row_at(Rows, i))) * build_input_segment(next, 0, N + 1, sublist(i + 1, M, Rows)) *
 undef_data_at(&((nodes + kept)->coef)) * undef_data_at(&((nodes + kept)->next)) *
 UCharArray::undef_seg(nodes, (kept + 1) * sizeof(struct InequList), M * sizeof(struct InequList)) *
 ((kept == 0 && emp) ||
  (0 < kept &&
   os_links(nodes, nodes + (kept - 1), sublist(0, kept - 1, os_shadows(nodes, 0, os_kept_prefix(N, i, Rows)))) *
   store(&((nodes + (kept - 1))->coef), build_row_coefficients(build_row_at(os_kept_prefix(N, i, Rows), kept - 1))) *
   store(&((nodes + (kept - 1))->next), 0)))
*/
        nodes[kept].coef = q->coef;
        nodes[kept].next = NULL;
        if (kept != 0) nodes[kept - 1].next = nodes + kept;
        ++kept;
    }
/*@ Assert exists (Masks : list Z),
 head == head@pre && variables == variables@pre && variables == N &&
 M == Zlength(Rows) && simplex_dimensions_ok(M, N) &&
 (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) && 0 <= N && N <= INT_MAX && sizeof(unsigned char) == 1 && rows == M &&
 kept == Zlength(os_kept(N, Rows)) && 0 <= kept && kept <= M &&
 simplex_dimensions_ok(kept, N) && (0 < kept => simplex_mpz_layout) &&
 simplex_malloc_token(signs, N) * UCharArray::full(signs, N, Masks) * simplex_malloc_token(nodes, M * sizeof(struct InequList)) * os_unborrowed_kept(N, head, Rows) *
 UCharArray::undef_seg(nodes, kept * sizeof(struct InequList), M * sizeof(struct InequList)) *
 ((kept == 0 && build_input_segment(0, 0, N + 1, os_shadows(nodes, 0, os_kept(N, Rows)))) ||
  (0 < kept && build_input_segment(nodes, 0, N + 1, os_shadows(nodes, 0, os_kept(N, Rows)))))
*/
    struct table t = build(kept ? nodes : NULL, variables);
/*@ Assert exists dPtr cPtr aPtr bPtr rowPtr nbPtr
 (dVals : list Z) (cVals : list Z) (aVals : list Z)
 (bVals : list Z) (rowVals : list Z) (nbVals : list Z),
 (forall (k : Z), (0 <= k && k < N) => Znth(k, nbVals, 0) == k) &&
 simplex_initial_table(N, kept, kept + N, build_matrix(os_kept(N, Rows)), dVals, cVals, aVals, bVals, rowVals) &&
 simplex_initial_equations(N, kept, kept + N, build_matrix(os_kept(N, Rows)), dVals, cVals, aVals, bVals) &&
 t.rows == kept && t.cols == kept + N &&
 t.d == dPtr && t.c == cPtr && t.a == aPtr &&
 t.basic == bPtr && t.row == rowPtr && t.nonbasic == nbPtr &&
 simplex_malloc_token(dPtr, kept * sizeof(__mpz_struct)) * MpzArray::full(dPtr, kept, dVals) *
 simplex_malloc_token(cPtr, kept * sizeof(__mpz_struct)) * MpzArray::full(cPtr, kept, cVals) *
 simplex_malloc_token(aPtr, kept * (kept + N) * sizeof(__mpz_struct)) * MpzArray::full(aPtr, kept * (kept + N), aVals) *
 simplex_malloc_token(bPtr, kept * sizeof(size_t)) * UIntArray::full(bPtr, kept, bVals) *
 simplex_malloc_token(rowPtr, (kept + N) * sizeof(size_t)) * UIntArray::full(rowPtr, kept + N, rowVals) *
 simplex_malloc_token(nbPtr, N * sizeof(size_t)) * UIntArray::full(nbPtr, N, nbVals) *
 build_input_segment(head, 0, N + 1, Rows) * simplex_malloc_token(nodes, M * sizeof(struct InequList)) * UCharArray::undef_full(nodes, M * sizeof(struct InequList)) *
 simplex_malloc_token(signs, N) * UCharArray::undef_full(signs, N) &&
 kept == Zlength(os_kept(N, Rows)) && rows == M && variables == N && head == head@pre
*/
    free(nodes);
    free(signs);
    return t;
}
