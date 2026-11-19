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
*/

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_one_sided_policy_opt_lib */
/*@ Extern Coq
 (os_node_layout : Prop)
 (os_coef : build_row_snapshot -> Z -> Z)
 (os_kept : Z -> list build_row_snapshot -> list build_row_snapshot)
 (os_size_relation : Z -> Z -> Prop)
 (os_mpz_without_size : Z -> Z -> Z -> Assertion)
*/

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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.violated_fme_model_selection_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.entering_fme_model_selection_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.pivot_fme_model_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.pivot_opt_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.sx_check_fme_model_lib */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.sx_check_qcp_opt_lib */
/*@ Extern Coq (scan_mpz_snapshot :: *) */
/*@ Extern Coq
    (scan_mpz_array : Z -> Z -> list Z -> list scan_mpz_snapshot -> Assertion)
    (scan_header_sizes : list scan_mpz_snapshot -> Z -> Z)
    (scan_row_values : list Z -> Z -> Z)
    (first_positive_row : Z -> Z -> list Z -> (Z -> Z) -> Z)
    (first_entering : Z -> Z -> list Z -> (Z -> Z) -> Z)
    (entering_row : Z -> Z -> (Z -> Z) -> Z -> Z)
    (entering_blocked_row : Z -> Z -> Z -> list Z -> Prop)
    (selection_basis : Z -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
    (selection_equations : Z -> Z -> Z -> list Constraint -> list Z -> list Z -> list Z -> list Z -> Prop)
    (pivot_nonbasic_columns : Z -> list Z -> list Z -> list Z -> Prop)
    (pivot_coef : list Z -> Z -> Z -> Z -> Z)
    (sx_entering_slot : list Z -> Z -> Z)
    (sx_entering_slot_matches : list Z -> Z -> Prop)
    (pivot_optimized_result : Z -> Z -> Z -> Z -> Z ->
      list Z -> list Z -> list Z -> list Z -> list Z -> list Z ->
      list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
    (sx_check_result : Z -> Z -> list Constraint -> Z -> Prop)
    (sx_zero_prefix : build_row_snapshot -> Z -> Prop)
*/

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
*/;

static size_t violated(const struct table *t, size_t variables)
/*@ valid_table_selection
  With (N : Z) (M : Z) (K : Z) (DP : Z) (CP : Z) (AP : Z) (BP : Z) (RP : Z)
       (D : list Z) (C : list Z) (A : list Z) (B : list Z) (R : list Z)
       (DT : list scan_mpz_snapshot) (CT : list scan_mpz_snapshot) (AT : list scan_mpz_snapshot)
  Require variables == N && 0 <= N && N <= K && K <= UINT_MAX && 0 <= M &&
          M * sizeof(__mpz_struct) <= INT_MAX && M * K * sizeof(__mpz_struct) <= INT_MAX &&
          M * sizeof(size_t) <= INT_MAX && K * sizeof(size_t) <= INT_MAX &&
          (0 < M => simplex_mpz_layout) &&
          selection_basis(M, K, D, A, B, R) &&
          t->rows == M && t->cols == K && t->d == DP && t->c == CP && t->a == AP &&
          t->basic == BP && t->row == RP &&
          simplex_malloc_token(DP, M * sizeof(__mpz_struct)) * scan_mpz_array(DP, M, D, DT) *
          simplex_malloc_token(CP, M * sizeof(__mpz_struct)) * scan_mpz_array(CP, M, C, CT) *
          simplex_malloc_token(AP, M * K * sizeof(__mpz_struct)) * scan_mpz_array(AP, M * K, A, AT) *
          simplex_malloc_token(BP, M * sizeof(size_t)) * UIntArray::full(BP, M, B) *
          simplex_malloc_token(RP, K * sizeof(size_t)) * UIntArray::full(RP, K, R)
  Ensure __return == first_positive_row(N, K, sublist(N, K, R), scan_header_sizes(CT)) &&
         __return == first_positive_row(N, K, sublist(N, K, R), scan_row_values(C)) &&
         selection_basis(M, K, D, A, B, R) &&
         t->rows == M && t->cols == K && t->d == DP && t->c == CP && t->a == AP &&
         t->basic == BP && t->row == RP &&
         simplex_malloc_token(DP, M * sizeof(__mpz_struct)) * scan_mpz_array(DP, M, D, DT) *
         simplex_malloc_token(CP, M * sizeof(__mpz_struct)) * scan_mpz_array(CP, M, C, CT) *
         simplex_malloc_token(AP, M * K * sizeof(__mpz_struct)) * scan_mpz_array(AP, M * K, A, AT) *
         simplex_malloc_token(BP, M * sizeof(size_t)) * UIntArray::full(BP, M, B) *
         simplex_malloc_token(RP, K * sizeof(size_t)) * UIntArray::full(RP, K, R)
*/;

static size_t entering(const struct table *t, size_t variables, size_t r)
/*@ valid_table_selection
  With (N : Z) (I : Z) (M : Z) (K : Z) (DP : Z) (CP : Z) (AP : Z) (BP : Z) (RP : Z)
       (D : list Z) (C : list Z) (A : list Z) (B : list Z) (R : list Z)
       (DT : list scan_mpz_snapshot) (CT : list scan_mpz_snapshot) (AT : list scan_mpz_snapshot)
  Require variables == N && r == I && 0 <= N && N <= K && 0 < K && K <= UINT_MAX &&
          0 <= I && I < M &&
          M * sizeof(__mpz_struct) <= INT_MAX && M * K * sizeof(__mpz_struct) <= INT_MAX &&
          M * sizeof(size_t) <= INT_MAX && K * sizeof(size_t) <= INT_MAX &&
          simplex_mpz_layout && selection_basis(M, K, D, A, B, R) &&
          t->rows == M && t->cols == K && t->d == DP && t->c == CP && t->a == AP &&
          t->basic == BP && t->row == RP &&
          simplex_malloc_token(DP, M * sizeof(__mpz_struct)) * scan_mpz_array(DP, M, D, DT) *
          simplex_malloc_token(CP, M * sizeof(__mpz_struct)) * scan_mpz_array(CP, M, C, CT) *
          simplex_malloc_token(AP, M * K * sizeof(__mpz_struct)) * scan_mpz_array(AP, M * K, A, AT) *
          simplex_malloc_token(BP, M * sizeof(size_t)) * UIntArray::full(BP, M, B) *
          simplex_malloc_token(RP, K * sizeof(size_t)) * UIntArray::full(RP, K, R)
  Ensure __return == first_entering(N, K, R, entering_row(I, K, scan_header_sizes(AT))) &&
         __return == first_entering(N, K, R, entering_row(I, K, scan_row_values(A))) &&
         (__return == SIZE_MAX => entering_blocked_row(N, K, I, A)) &&
         selection_basis(M, K, D, A, B, R) &&
         t->rows == M && t->cols == K && t->d == DP && t->c == CP && t->a == AP &&
         t->basic == BP && t->row == RP &&
         simplex_malloc_token(DP, M * sizeof(__mpz_struct)) * scan_mpz_array(DP, M, D, DT) *
         simplex_malloc_token(CP, M * sizeof(__mpz_struct)) * scan_mpz_array(CP, M, C, CT) *
         simplex_malloc_token(AP, M * K * sizeof(__mpz_struct)) * scan_mpz_array(AP, M * K, A, AT) *
         simplex_malloc_token(BP, M * sizeof(size_t)) * UIntArray::full(BP, M, B) *
         simplex_malloc_token(RP, K * sizeof(size_t)) * UIntArray::full(RP, K, R)
*/;

static void pivot(struct table *t, size_t r, size_t e)
/*@ nonzero_pivot_at_entering_slot
    With M K I E DP CP AP BP RP NP (D : list Z) (C : list Z) (A : list Z) (B : list Z) (R : list Z) (N : list Z)
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
        sx_entering_slot_matches(N, E) &&
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
        pivot_optimized_result(M, K, I, E, sx_entering_slot(N, E), D, C, A, B, R, N, Df, Cf, Af, Bf, Rf, Nf) &&
        MpzArray::full(DP, M, Df) *
        MpzArray::full(CP, M, Cf) *
        MpzArray::full(AP, M*K, Af) *
        UIntArray::full(BP, M, Bf) *
        UIntArray::full(RP, K, Rf) *
        UIntArray::full(NP, K-M, Nf)
*/;

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
*/;

int sx_check_qcp(const struct InequList *head, size_t variables)
/*@ rational_feasibility_normal
    With (N : Z) (M : Z) (Rows : list build_row_snapshot)
    Require variables == N && M == Zlength(Rows) &&
            simplex_dimensions_ok(M, N) &&
            (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) &&
            build_input_segment(head, 0, N + 1, Rows)
    Ensure sx_check_result(N, M, build_matrix(Rows), __return) &&
           build_input_segment(head, 0, N + 1, Rows)
*/
{
    /* A positive constant-only input row is already a contradiction. */
    /*@ Inv Assert exists (i : Z),
          head == head@pre && variables == N && M == Zlength(Rows) &&
          simplex_dimensions_ok(M, N) &&
          (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) &&
          0 <= i && i <= M &&
          build_input_segment(head, q, N + 1, sublist(0, i, Rows)) *
          build_input_segment(q, 0, N + 1, sublist(i, M, Rows))
    */
    for (const struct InequList *q = head; q; q = q->next) {
        /*@ Assert exists (i : Z) (coef : Z) (next : Z) (sz : Z),
          head == head@pre && variables == N && M == Zlength(Rows) &&
          simplex_dimensions_ok(M, N) &&
          (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) &&
          q != 0 && 0 <= i && i < M && coef != 0 &&
          coef == build_row_coefficients(build_row_at(Rows, i)) &&
          next == build_row_next(build_row_at(Rows, i)) &&
          os_size_relation(sz, Znth(0, build_row_entries(build_row_at(Rows, i)), 0)) &&
          build_input_segment(head, q, N + 1, sublist(0, i, Rows)) *
          store(&(q->next), next) * store(&(q->coef), coef) *
          build_input_segment(next, 0, N + 1, sublist(i + 1, M, Rows)) *
          data_at(&(((mpz_ptr)coef)[0]._mp_size), int, sz) *
          os_mpz_without_size((mpz_ptr)coef, Znth(0, build_row_entries(build_row_at(Rows, i)), 0), sz) *
          MpzArray::missing_i(coef, 0, 0, N + 1, build_row_entries(build_row_at(Rows, i)))
        */
        if (q->coef[0]._mp_size <= 0) continue;
        size_t j = 0;
        /*@ Inv Assert exists (i : Z) (coef : Z) (next : Z),
          head == head@pre && variables == N && M == Zlength(Rows) &&
          simplex_dimensions_ok(M, N) &&
          (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) &&
          q != 0 && 0 <= i && i < M && coef != 0 &&
          coef == build_row_coefficients(build_row_at(Rows, i)) &&
          next == build_row_next(build_row_at(Rows, i)) &&
          0 <= j && j <= N &&
          0 < Znth(0, build_row_entries(build_row_at(Rows, i)), 0) &&
          sx_zero_prefix(build_row_at(Rows, i), j) &&
          build_input_segment(head, q, N + 1, sublist(0, i, Rows)) *
          store(&(q->next), next) * store(&(q->coef), coef) *
          build_input_segment(next, 0, N + 1, sublist(i + 1, M, Rows)) *
          ((j == N && MpzArray::full(coef, N + 1, build_row_entries(build_row_at(Rows, i)))) ||
           (exists (sz : Z), j < N &&
            os_size_relation(sz, os_coef(build_row_at(Rows, i), j)) &&
            data_at(&(((mpz_ptr)coef)[j + 1]._mp_size), int, sz) *
            os_mpz_without_size(((mpz_ptr)coef) + (j + 1), os_coef(build_row_at(Rows, i), j), sz) *
            MpzArray::missing_i(coef, j + 1, 0, N + 1, build_row_entries(build_row_at(Rows, i)))))
        */
        while (j < variables && q->coef[j + 1]._mp_size == 0) ++j;
        if (j == variables) return 1;
    }
    /*@ Assert head == head@pre && variables == N && M == Zlength(Rows) &&
          simplex_dimensions_ok(M, N) &&
          (0 < M => simplex_mpz_layout) && (0 < M => os_node_layout) &&
          build_input_segment(head, 0, N + 1, Rows)
    */
    struct table t = build_one_sided(head, variables);
    int result;
    /*@ Inv Assert
          exists P K DP CP AP BP RP NP (D : list Z) (C : list Z) (A : list Z) (B : list Z) (R : list Z) (NB : list Z),
          head == head@pre && variables == N && M == Zlength(Rows) &&
          P == Zlength(os_kept(N, Rows)) && K == P + N &&
          simplex_dimensions_ok(P, N) && (0 < P => simplex_mpz_layout) &&
          selection_basis(P, K, D, A, B, R) &&
          pivot_nonbasic_columns(K, B, R, NB) &&
          selection_equations(N, P, K, build_matrix(os_kept(N, Rows)), D, C, A, B) &&
          t.rows == P && t.cols == K && t.d == DP && t.c == CP && t.a == AP &&
          t.basic == BP && t.row == RP && t.nonbasic == NP &&
          undef_data_at(&result) * build_input_segment(head, 0, N + 1, Rows) *
          simplex_malloc_token(DP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(CP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(AP, P * K * sizeof(__mpz_struct)) *
          simplex_malloc_token(BP, P * sizeof(size_t)) *
          simplex_malloc_token(RP, K * sizeof(size_t)) *
          simplex_malloc_token(NP, N * sizeof(size_t)) * MpzArray::full(DP, P, D) * MpzArray::full(CP, P, C) *
          MpzArray::full(AP, P * K, A) * UIntArray::full(BP, P, B) * UIntArray::full(RP, K, R) *
          UIntArray::full(NP, N, NB)
    */
    for (;;) {
        /*@ Assert
          exists P K DP CP AP BP RP NP (D : list Z) (C : list Z) (A : list Z) (B : list Z) (R : list Z) (NB : list Z)
                 (DT : list scan_mpz_snapshot) (CT : list scan_mpz_snapshot)
                 (AT : list scan_mpz_snapshot),
          head == head@pre && variables == N && M == Zlength(Rows) &&
          P == Zlength(os_kept(N, Rows)) && K == P + N &&
          simplex_dimensions_ok(P, N) && (0 < P => simplex_mpz_layout) &&
          selection_basis(P, K, D, A, B, R) &&
          pivot_nonbasic_columns(K, B, R, NB) &&
          selection_equations(N, P, K, build_matrix(os_kept(N, Rows)), D, C, A, B) &&
          t.rows == P && t.cols == K && t.d == DP && t.c == CP && t.a == AP &&
          t.basic == BP && t.row == RP && t.nonbasic == NP &&
          undef_data_at(&result) * build_input_segment(head, 0, N + 1, Rows) *
          simplex_malloc_token(DP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(CP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(AP, P * K * sizeof(__mpz_struct)) *
          simplex_malloc_token(BP, P * sizeof(size_t)) *
          simplex_malloc_token(RP, K * sizeof(size_t)) *
          simplex_malloc_token(NP, N * sizeof(size_t)) * scan_mpz_array(DP, P, D, DT) * scan_mpz_array(CP, P, C, CT) *
          scan_mpz_array(AP, P * K, A, AT) * UIntArray::full(BP, P, B) * UIntArray::full(RP, K, R) *
          UIntArray::full(NP, N, NB)
        */
        size_t r = violated(&t, variables);
        if (r == SIZE_MAX) {
            result = 0;
            break;
        }
        size_t e = entering(&t, variables, r);
        if (e == SIZE_MAX) {
            result = 1;
            break;
        }
        /*@ Assert
          exists P K DP CP AP BP RP NP (D : list Z) (C : list Z) (A : list Z) (B : list Z) (R : list Z) (NB : list Z),
          head == head@pre && variables == N && M == Zlength(Rows) &&
          P == Zlength(os_kept(N, Rows)) && K == P + N &&
          simplex_dimensions_ok(P, K - P) && (0 < P => simplex_mpz_layout) &&
          simplex_mpz_layout &&
          selection_basis(P, K, D, A, B, R) &&
          pivot_nonbasic_columns(K, B, R, NB) &&
          selection_equations(N, P, K, build_matrix(os_kept(N, Rows)), D, C, A, B) &&
          0 <= r && r < P && 0 <= e && e < K &&
          R[e] == SIZE_MAX && pivot_coef(A, K, r, e) != 0 &&
          sx_entering_slot_matches(NB, e) && Zlength(NB) == K - P &&
          t.rows == P && t.cols == K && t.d == DP && t.c == CP && t.a == AP &&
          t.basic == BP && t.row == RP && t.nonbasic == NP &&
          undef_data_at(&result) * build_input_segment(head, 0, N + 1, Rows) *
          simplex_malloc_token(DP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(CP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(AP, P * K * sizeof(__mpz_struct)) *
          simplex_malloc_token(BP, P * sizeof(size_t)) *
          simplex_malloc_token(RP, K * sizeof(size_t)) *
          simplex_malloc_token(NP, N * sizeof(size_t)) * MpzArray::full(DP, P, D) * MpzArray::full(CP, P, C) *
          MpzArray::full(AP, P * K, A) * UIntArray::full(BP, P, B) * UIntArray::full(RP, K, R) *
          UIntArray::full(NP, K - P, NB)
        */
        pivot(&t, r, e);
    }
    /*@ Assert
          exists P DP CP AP BP RP NP (D : list Z) (C : list Z) (A : list Z),
          head == head@pre && variables == N && M == Zlength(Rows) &&
          simplex_dimensions_ok(P, N) && (0 < P => simplex_mpz_layout) &&
          sx_check_result(N, M, build_matrix(Rows), result) &&
          t.rows == P && t.cols == P + N && t.d == DP && t.c == CP && t.a == AP &&
          t.basic == BP && t.row == RP && t.nonbasic == NP &&
          build_input_segment(head, 0, N + 1, Rows) *
          simplex_malloc_token(DP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(CP, P * sizeof(__mpz_struct)) *
          simplex_malloc_token(AP, P * (P + N) * sizeof(__mpz_struct)) *
          simplex_malloc_token(BP, P * sizeof(size_t)) *
          simplex_malloc_token(RP, (P + N) * sizeof(size_t)) *
          simplex_malloc_token(NP, N * sizeof(size_t)) * MpzArray::full(DP, P, D) * MpzArray::full(CP, P, C) *
          MpzArray::full(AP, P * (P + N), A) * UCharArray::undef_full(BP, P * sizeof(size_t)) *
          UCharArray::undef_full(RP, (P + N) * sizeof(size_t)) *
          UCharArray::undef_full(NP, N * sizeof(size_t))
    */
    destroy(&t);
    return result;
}
