#include "sx_solver_contract.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "FAIL %d: %s\n", __LINE__, #x);                                        \
            exit(1);                                                                               \
        }                                                                                          \
    } while (0)
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};
typedef struct {
    struct { size_t rows, variables; } p;
    SxRat *owned;
    __mpz_struct *view;
    struct InequList *nodes;
    size_t count;
} Input;
static Input make(size_t m, size_t n, const char *const *values) {
    Input a = {{m, n}, NULL, NULL, NULL, m * (n + 1)};
    a.owned = calloc(a.count ? a.count : 1, sizeof(*a.owned));
    a.view = calloc(a.count ? a.count : 1, sizeof(*a.view));
    a.nodes = calloc(m ? m : 1, sizeof(*a.nodes));
    CHECK(a.owned && a.view && a.nodes);
    for (size_t i = 0; i < a.count; i++) {
        sx_rat_init(&a.owned[i]);
        CHECK(sx_rat_set(&a.owned[i], values[i], "1", NULL, NULL) == SX_OK);
        a.view[i] = a.owned[i].num;
    }
    for (size_t i = 0; i < m; i++) {
        a.nodes[i].coef = a.view + i * (n + 1);
        a.nodes[i].next = i + 1 < m ? &a.nodes[i + 1] : NULL;
    }
    return a;
}
static void destroy(Input *a) {
    for (size_t i = 0; i < a->count; i++)
        sx_rat_clear(&a->owned[i]);
    free(a->owned);
    free(a->view);
    free(a->nodes);
}
static void invoke(const Input *a, unsigned flags, const SxSolverLimits *base,
                   SxResult *r) {
    SxSolverLimits l = base ? *base : (SxSolverLimits){0};
    l.disable_optimizations = flags;
    sx_check_qcp(a->p.rows ? a->nodes : NULL, a->p.variables, &l, r);
}
static void eq(const SxRat *a, const SxRat *b) {
    int c;
    CHECK(sx_rat_cmp(&c, a, b, NULL, NULL) == SX_OK && c == 0);
}
static void integer_eq(const SxRat *a, const char *value) {
    SxRat b;
    sx_rat_init(&b);
    CHECK(sx_rat_set(&b, value, "1", NULL, NULL) == SX_OK);
    eq(a, &b);
    sx_rat_clear(&b);
}
static void none(const SxResult *r) {
    CHECK(!r->witness && !r->witness_length && !r->conflict.present && !r->conflict.blockers &&
          !r->conflict.blocker_count);
}
/* Independent exact affine substitution into the ORIGINAL integer rows. */
static void conflict_identity(const Input *a, const SxResult *r) {
    const SxConflict *c = &r->conflict;
    size_t n = a->p.variables;
    CHECK(c->present && c->row < a->p.rows && c->basic_variable == n + c->bound_source_row &&
          c->bound_source_row < a->p.rows);
    SxRat left, right, coef, product, total;
    sx_rat_init(&left);
    sx_rat_init(&right);
    sx_rat_init(&coef);
    sx_rat_init(&product);
    sx_rat_init(&total);
    for (size_t j = 0; j <= n; j++) {
        CHECK(sx_rat_import(&left, &a->view[c->bound_source_row * (n + 1) + j], NULL, NULL) ==
              SX_OK);
        sx_rat_clear(&right);
        if (!j)
            CHECK(sx_rat_op(&right, '+', &right, &c->constant, NULL, NULL) == SX_OK);
        for (size_t k = 0; k < c->blocker_count; k++) {
            const SxBlocker *b = &c->blockers[k];
            CHECK(b->source_row < a->p.rows && b->variable == n + b->source_row);
            CHECK(!b->is_lower);
            CHECK(b->coefficient.num._mp_size < 0);
            integer_eq(&b->bound, "0");
            CHECK(sx_rat_import(&coef, &a->view[b->source_row * (n + 1) + j], NULL, NULL) == SX_OK);
            CHECK(sx_rat_op(&product, '*', &coef, &b->coefficient, NULL, NULL) == SX_OK);
            CHECK(sx_rat_op(&right, '+', &right, &product, NULL, NULL) == SX_OK);
        }
        eq(&left, &right);
    }
    CHECK(sx_rat_op(&total, '+', &total, &c->constant, NULL, NULL) == SX_OK);
    for (size_t k = 0; k < c->blocker_count; k++) {
        CHECK(sx_rat_op(&product, '*', &c->blockers[k].coefficient, &c->blockers[k].bound, NULL,
                        NULL) == SX_OK);
        CHECK(sx_rat_op(&total, '+', &total, &product, NULL, NULL) == SX_OK);
    }
    eq(&total, &c->attainable);
    int cmp;
    CHECK(sx_rat_cmp(&cmp, &c->attainable, &c->required, NULL, NULL) == SX_OK && cmp > 0);
    sx_rat_clear(&left);
    sx_rat_clear(&right);
    sx_rat_clear(&coef);
    sx_rat_clear(&product);
    sx_rat_clear(&total);
}
static size_t injected;
static void faults(const Input *a, unsigned flags) {
    SxResult r;
    sx_result_init(&r);
    size_t baseline = sx_runtime_live_bytes();
    invoke(a, flags, NULL, &r);
    CHECK(r.error == SX_OK &&
          (r.rational_status == SX_Q_FEASIBLE || r.rational_status == SX_Q_UNSAT));
    size_t count = r.stats.allocations, peak = r.stats.peak_bytes;
    sx_result_clear(&r);
    for (size_t i = 1; i <= count; i++) {
        SxSolverLimits l = {0};
        l.fail_at = i;
        invoke(a, flags, &l, &r);
        CHECK(r.error == SX_OOM && r.rational_status == SX_Q_NOT_RUN &&
              r.integer_status == SX_Z_NOT_DECIDED && r.diagnostic == SX_D_ALLOC);
        none(&r);
        CHECK(r.stats.allocations == i);
        sx_result_clear(&r);
        CHECK(sx_runtime_live_bytes() == baseline);
        injected++;
    }
    SxSolverLimits l = {0};
    l.max_table_bytes = peak;
    invoke(a, flags, &l, &r);
    CHECK(r.error == SX_OK && r.rational_status != SX_Q_UNKNOWN);
    sx_result_clear(&r);
    l.max_table_bytes = peak - 1;
    invoke(a, flags, &l, &r);
    CHECK(r.error == SX_OK && r.rational_status == SX_Q_UNKNOWN && r.reason == SX_REASON_SPACE);
    none(&r);
    sx_result_clear(&r);
    CHECK(sx_runtime_live_bytes() == baseline);
}
int main(void) {
    const char *feasible[] = {"-12", "0",  "0",   "0",  "0", "0", "6", "-6", "0",  "0", "0",
                              "0",   "-4", "4",   "0",  "0", "0", "0", "0",  "0",  "0", "0",
                              "0",   "0",  "-10", "0",  "0", "0", "0", "0",  "10", "0", "-5",
                              "0",   "0",  "0",   "-8", "0", "4", "0", "0",  "0"};
    Input a = make(7, 5, feasible);
    SxResult baseline, r;
    sx_result_init(&baseline);
    sx_result_init(&r);
    invoke(&a, SX_OPT_ALL, NULL, &baseline);
    CHECK(baseline.rational_status == SX_Q_FEASIBLE && baseline.integer_status == SX_Z_SAT);
    for (unsigned flags = 0; flags <= SX_OPT_ALL; flags++) {
        SxSolverLimits l = {0};
        l.collect_matrix_stats = 1;
        invoke(&a, flags, &l, &r);
        CHECK(r.error == SX_OK && r.rational_status == baseline.rational_status &&
              r.integer_status == baseline.integer_status && r.witness_length == 5 &&
              r.stats.verified_rows == 7);
        for (size_t i = 0; i < 5; i++)
            eq(&r.witness[i], &baseline.witness[i]);
        CHECK(r.stats.input_nonzeros == 4 && r.stats.input_cells == 35);
        CHECK(r.stats.matrix_snapshots == r.stats.pivots + 1 &&
              r.stats.matrix_cells_scanned >= r.stats.table_cells);
        if (!flags) {
            CHECK(r.stats.active_rows == 4 && r.stats.active_variables == 2 &&
                  r.stats.dropped_true_rows == 3 && r.stats.removed_variables == 3 &&
                  r.stats.gcd_reduced_rows == 4);
        }
        CHECK(r.stats.arithmetic.rat_import > 0 && r.stats.arithmetic.big_gcd > 0);
        sx_result_clear(&r);
    }
    sx_result_clear(&baseline);
    destroy(&a);
    /* Skipped original rows, unequal factors, multiple blockers and duplicate row. */
    const char *unsat[] = {"-9",  "0", "0", "0", "0", "6",  "-6",  "0", "0",  "0",
                           "0",   "0", "0", "0", "0", "14", "0",   "0", "-7", "0",
                           "-8", "4", "0", "4", "0", "12", "-12", "0", "0",  "0"};
    a = make(6, 4, unsat);
    for (unsigned flags = 0; flags <= SX_OPT_ALL; flags++) {
        invoke(&a, flags, NULL, &r);
        CHECK(r.error == SX_OK && r.rational_status == SX_Q_UNSAT &&
              r.integer_status == SX_Z_UNSAT);
        conflict_identity(&a, &r);
        if (!flags)
            CHECK(r.conflict.blocker_count == 2);
        sx_result_clear(&r);
    }
    destroy(&a);
    const char *small[] = {"0",
                           "0",
                           "0",
                           "18446744073709551616",
                           "-18446744073709551616",
                           "0",
                           "-55340232221128654848",
                           "55340232221128654848",
                           "0"};
    a = make(3, 2, small);
    faults(&a, 0);
    faults(&a, SX_OPT_ALL);
    destroy(&a);
    const char *constant[] = {"7", "0", "0", "0", "0", "0"};
    a = make(2, 2, constant);
    faults(&a, 0);
    for (unsigned flags = 0; flags <= SX_OPT_ALL; flags++) {
        invoke(&a, flags, NULL, &r);
        CHECK(r.error == SX_OK && r.rational_status == SX_Q_UNSAT &&
              r.conflict.basic_variable == 2 && r.conflict.row == 0 &&
              r.conflict.bound_source_row == 0);
        conflict_identity(&a, &r);
        sx_result_clear(&r);
    }
    /* The later illegal object must win over an earlier constant contradiction. */
    unsigned int zero = 0;
    __mpz_struct save = a.view[4];
    a.view[4] = (__mpz_struct){0, 1, &zero};
    for (unsigned flags = 0; flags <= SX_OPT_ALL; flags++) {
        invoke(&a, flags, NULL, &r);
        CHECK(r.error == SX_INVALID && r.rational_status == SX_Q_NOT_RUN);
        none(&r);
        sx_result_clear(&r);
    }
    a.view[4] = save;
    /* Structural errors belong to the top-level validator in every mode,
       including the uncompressed path handed to the private table builder. */
    mpz_ptr saved_coef = a.nodes[1].coef;
    a.nodes[1].coef = NULL;
    for (unsigned flags = 0; flags <= SX_OPT_ALL; flags++) {
        invoke(&a, flags, NULL, &r);
        CHECK(r.error == SX_INVALID && r.rational_status == SX_Q_NOT_RUN &&
              r.diagnostic == SX_D_OBJECT);
        none(&r);
        sx_result_clear(&r);
    }
    a.nodes[1].coef = saved_coef;
    a.nodes[1].next = &a.nodes[0];
    for (unsigned flags = 0; flags <= SX_OPT_ALL; flags++) {
        invoke(&a, flags, NULL, &r);
        CHECK(r.error == SX_INVALID && r.diagnostic == SX_D_CYCLE);
        none(&r);
        sx_result_clear(&r);
    }
    a.nodes[1].next = NULL;
    destroy(&a);
    /* Identity GCD=1 row: no normalized coefficient copy is kept or second import pass. */
    const char *identity[] = {"1", "-2"};
    a = make(1, 1, identity);
    invoke(&a, 0, NULL, &r);
    CHECK(r.error == SX_OK && r.stats.preprocess_coefficients_scanned == 2 &&
          r.stats.gcd_reduced_rows == 0 && r.stats.matrix_snapshots == 0 &&
          r.stats.matrix_cells_scanned == 0);
    sx_result_clear(&r);
    SxSolverLimits bad = {0};
    bad.disable_optimizations = 16;
    sx_check_qcp(a.nodes, a.p.variables, &bad, &r);
    CHECK(r.error == SX_INVALID && r.diagnostic == SX_D_ARGUMENT);
    sx_result_clear(&r);
    destroy(&a);
    CHECK(sx_runtime_live_bytes() == 0 && sx_live_blocks() == 0);
    printf("P4 tests passed: 16 masks through the list entry, original affine conflicts, %zu "
           "individually injected failures and exact total-space boundaries\n",
           injected);
    return 0;
}
