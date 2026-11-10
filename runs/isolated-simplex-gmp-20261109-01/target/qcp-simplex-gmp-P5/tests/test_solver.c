#include "sx_solver_contract.h"
#include <limits.h>
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
static unsigned int regression_disable;
static void regression_qcp(const struct InequList *p, size_t n, const SxSolverLimits *l,
                           SxResult *r) {
    SxSolverLimits effective = l ? *l : (SxSolverLimits){0};
    effective.disable_optimizations = regression_disable;
    sx_check_qcp(p, n, &effective, r);
}
#define sx_check_qcp regression_qcp
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};
typedef struct {
    struct { size_t rows, variables; } p;
    SxRat *owned;
    __mpz_struct *view;
    size_t count;
    struct InequList *nodes;
} Input;
static Input input(size_t m, size_t n, const char *const *strings) {
    Input a = {{m, n}, NULL, NULL, m * (n + 1), NULL};
    a.owned = calloc(a.count ? a.count : 1, sizeof(*a.owned));
    a.view = calloc(a.count ? a.count : 1, sizeof(*a.view));
    CHECK(a.owned && a.view);
    for (size_t i = 0; i < a.count; i++) {
        sx_rat_init(&a.owned[i]);
        CHECK(sx_rat_set(&a.owned[i], strings[i], "1", NULL, NULL) == SX_OK);
        a.view[i] = a.owned[i].num;
    }
    a.nodes = m ? calloc(m, sizeof(*a.nodes)) : NULL;
    CHECK(!m || a.nodes);
    for (size_t i = 0; i < m; i++) {
        a.nodes[i].coef = a.view + i * (n + 1);
        a.nodes[i].next = i + 1 < m ? &a.nodes[i + 1] : NULL;
    }
    return a;
}
static void clear(Input *a) {
    for (size_t i = 0; i < a->count; i++)
        sx_rat_clear(&a->owned[i]);
    free(a->owned);
    free(a->view);
    free(a->nodes);
}
static void eq(const SxRat *q, const char *expected) {
    char *s = NULL;
    CHECK(sx_rat_string(&s, q, NULL, NULL) == SX_OK);
    CHECK(!strcmp(s, expected));
    sx_string_free(s);
}
static void no_output(const SxResult *r) {
    CHECK(!r->witness && r->witness_length == 0 && !r->conflict.present && !r->conflict.blockers &&
          r->conflict.blocker_count == 0);
}
static void good_at(const SxResult *r, SxQStatus q, SxZStatus z, int line) {
    if (!(r->error == SX_OK && r->rational_status == q && r->integer_status == z))
        fprintf(stderr, "line %d got e%d q%d z%d reason%d diag%d expected q%d z%d\n", line,
                r->error, r->rational_status, r->integer_status, r->reason, r->diagnostic, q, z);
    CHECK(r->error == SX_OK && r->rational_status == q && r->integer_status == z);
    if (q == SX_Q_FEASIBLE) {
        CHECK(!r->conflict.present);
        CHECK(r->diagnostic == SX_D_NONE);
    }
    if (q == SX_Q_UNSAT) {
        CHECK(!r->witness && r->witness_length == 0 && r->conflict.present &&
              r->reason == SX_REASON_CONFLICT);
    }
}
#define good(r, q, z) good_at((r), (q), (z), __LINE__)
static void evidence(const SxResult *r) {
    const SxConflict *c = &r->conflict;
    CHECK(c->present);
    SxRat sum, p;
    sx_rat_init(&sum);
    sx_rat_init(&p);
    CHECK(sx_rat_op(&sum, '+', &c->constant, &sum, NULL, NULL) == SX_OK);
    for (size_t i = 0; i < c->blocker_count; i++) {
        const SxBlocker *b = &c->blockers[i];
        CHECK(b->source_row != SIZE_MAX);
        CHECK(b->is_lower == (c->to_lower ? (b->coefficient.num._mp_size < 0)
                                          : (b->coefficient.num._mp_size > 0)));
        CHECK(sx_rat_op(&p, '*', &b->coefficient, &b->bound, NULL, NULL) == SX_OK);
        CHECK(sx_rat_op(&sum, '+', &sum, &p, NULL, NULL) == SX_OK);
    }
    int cmp;
    CHECK(sx_rat_cmp(&cmp, &sum, &c->attainable, NULL, NULL) == SX_OK && cmp == 0);
    CHECK(sx_rat_cmp(&cmp, &c->attainable, &c->required, NULL, NULL) == SX_OK &&
          (c->to_lower ? cmp < 0 : cmp > 0));
    sx_rat_clear(&sum);
    sx_rat_clear(&p);
}
static size_t faults;
static void failures(Input *a) {
    size_t baseline = sx_runtime_live_bytes();
    SxResult r;
    sx_result_init(&r);
    sx_check_qcp(a->nodes, a->p.variables, NULL, &r);
    CHECK(r.error == SX_OK && r.rational_status != SX_Q_UNKNOWN);
    size_t count = r.stats.allocations, peak = r.stats.peak_bytes;
    sx_result_clear(&r);
    CHECK(sx_runtime_live_bytes() == baseline);
    for (size_t k = 1; k <= count; k++) {
        SxSolverLimits l = {0};
        l.fail_at = k;
        sx_check_qcp(a->nodes, a->p.variables, &l, &r);
        CHECK(r.error == SX_OOM && r.rational_status == SX_Q_NOT_RUN &&
              r.integer_status == SX_Z_NOT_DECIDED && r.reason == SX_REASON_ALLOCATION &&
              r.diagnostic == SX_D_ALLOC);
        no_output(&r);
        CHECK(r.stats.allocations == k);
        sx_result_clear(&r);
        CHECK(sx_runtime_live_bytes() == baseline);
        faults++;
    }
    SxSolverLimits l = {0};
    l.max_table_bytes = peak;
    sx_check_qcp(a->nodes, a->p.variables, &l, &r);
    CHECK(r.error == SX_OK && r.rational_status != SX_Q_UNKNOWN);
    sx_result_clear(&r);
    l.max_table_bytes = peak - 1;
    sx_check_qcp(a->nodes, a->p.variables, &l, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_SPACE && r.diagnostic == SX_D_TOTAL_BYTES);
    no_output(&r);
    sx_result_clear(&r);
    CHECK(sx_runtime_live_bytes() == baseline);
}
int main(void) {
    const char *flags = getenv("SX_TEST_DISABLE_OPTS");
    if (flags) {
        unsigned long v = strtoul(flags, NULL, 10);
        CHECK(v <= SX_OPT_ALL);
        regression_disable = (unsigned int)v;
    }
    SxResult r;
    sx_result_init(&r);
    sx_check_qcp(NULL, 0, NULL, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    CHECK(r.witness_length == 0 && r.stats.pivots == 0);
    sx_result_clear(&r);
    sx_result_clear(&r);
    const char *truth[] = {"-1"}, *lie[] = {"1"}, *simple[] = {"1", "-1"},
               *fraction[] = {"1", "-2", "-1", "2"}, *conflict[] = {"1", "-1", "0", "1"};
    Input a = input(1, 0, truth);
    sx_check_qcp(a.nodes, a.p.variables, NULL, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    CHECK(r.stats.verified_rows == 1);
    sx_result_clear(&r);
    clear(&a);
    a = input(1, 0, lie);
    sx_check_qcp(a.nodes, a.p.variables, NULL, &r);
    good(&r, SX_Q_UNSAT, SX_Z_UNSAT);
    CHECK(r.stats.pivots == 0 && r.conflict.blocker_count == 0);
    evidence(&r);
    sx_result_clear(&r);
    failures(&a);
    clear(&a);
    a = input(1, 1, simple);
    __mpz_struct saved[2];
    memcpy(saved, a.view, sizeof saved);
    sx_check_qcp(a.nodes, a.p.variables, NULL, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    eq(&r.witness[0], "1/1");
    CHECK(r.stats.pivots == 1 && r.stats.verified_rows == 1 &&
          !memcmp(saved, a.view, sizeof saved));
    sx_result_clear(&r);
    failures(&a);
    clear(&a);
    a = input(2, 1, fraction);
    SxSolverLimits limit = {0};
    limit.max_pivots = 1;
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_FRACTIONAL && r.stats.pivots == 1);
    eq(&r.witness[0], "1/2");
    sx_result_clear(&r);
    clear(&a);
    a = input(2, 1, conflict);
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_UNSAT, SX_Z_UNSAT);
    CHECK(r.stats.pivots == 1 && r.conflict.blocker_count == 1);
    evidence(&r);
    sx_result_clear(&r);
    failures(&a);
    clear(&a);
    const char *unique[] = {"-3", "1", "1", "3", "-1", "-1", "-1", "1", "-1", "1", "-1", "1"};
    a = input(4, 2, unique);
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_PIVOTS && r.stats.pivots == 1);
    no_output(&r);
    sx_result_clear(&r);
    limit.max_pivots = 2;
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    eq(&r.witness[0], "2/1");
    eq(&r.witness[1], "1/1");
    CHECK(r.stats.pivots == 2 && r.stats.verified_rows == 4);
    sx_result_clear(&r);
    clear(&a);
    /* Witness memory is owned and survives destruction of original input. */
    const char *large[] = {"1", "-1000000000000000000000000000000", "-1",
                           "1000000000000000000000000000000"};
    a = input(2, 1, large);
    sx_check_qcp(a.nodes, a.p.variables, NULL, &r);
    clear(&a);
    good(&r, SX_Q_FEASIBLE, SX_Z_UNKNOWN);
    eq(&r.witness[0], "1/1000000000000000000000000000000");
    sx_result_clear(&r);
    /* Evidence memory is independent of both input and destroyed internal table. */
    a = input(2, 1, conflict);
    sx_check_qcp(a.nodes, a.p.variables, NULL, &r);
    clear(&a);
    good(&r, SX_Q_UNSAT, SX_Z_UNSAT);
    evidence(&r);
    sx_result_clear(&r);
    a = input(1, 1, simple);
    limit = (SxSolverLimits){0};
    limit.max_table_bytes = 1;
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_SPACE);
    no_output(&r);
    sx_result_clear(&r);
    limit = (SxSolverLimits){0};
    limit.arithmetic.max_bytes = 1;
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_ARITH_SPACE);
    no_output(&r);
    sx_result_clear(&r);
    clear(&a);
    a = input(2, 1, large);
    limit = (SxSolverLimits){0};
    limit.arithmetic.max_limbs = 4;
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_LIMBS);
    no_output(&r);
    sx_result_clear(&r);
    clear(&a);
    /* Input/object/limit errors are not resource UNKNOWN. */
    limit = (SxSolverLimits){0};
    limit.arithmetic.max_limbs = 3;
    sx_check_qcp(NULL, 0, &limit, &r);
    CHECK(r.error == SX_INVALID);
    sx_result_clear(&r);
    limit = (SxSolverLimits){0};
    limit.arithmetic.fail_at = 1;
    sx_check_qcp(NULL, 0, &limit, &r);
    CHECK(r.error == SX_INVALID);
    sx_result_clear(&r);
    unsigned int zero = 0;
    __mpz_struct malformed = {0, 1, &zero};
    struct InequList bad = {&malformed, NULL};
    sx_check_qcp(&bad, 0, NULL, &r);
    CHECK(r.error == SX_INVALID && r.diagnostic == SX_D_OBJECT);
    no_output(&r);
    sx_result_clear(&r);
    malformed._mp_size = INT_MIN;
    sx_check_qcp(&bad, 0, NULL, &r);
    CHECK(r.error == SX_INVALID);
    sx_result_clear(&r);
    /* Validate final-node data, multi-node cycles, and a self-loop. */
    a = input(2, 1, conflict);
    __mpz_struct *coef = a.nodes[1].coef;
    a.nodes[1].coef = NULL;
    sx_check_qcp(a.nodes, 1, NULL, &r);
    CHECK(r.error == SX_INVALID && r.diagnostic == SX_D_OBJECT);
    no_output(&r);
    sx_result_clear(&r);
    a.nodes[1].coef = coef;
    a.nodes[1].next = &a.nodes[0];
    sx_check_qcp(a.nodes, 1, NULL, &r);
    CHECK(r.error == SX_INVALID && r.diagnostic == SX_D_CYCLE);
    no_output(&r);
    sx_result_clear(&r);
    a.nodes[1].next = NULL;
    a.nodes[0].next = &a.nodes[0];
    sx_check_qcp(a.nodes, 1, NULL, &r);
    CHECK(r.error == SX_INVALID && r.diagnostic == SX_D_CYCLE);
    sx_result_clear(&r);
    a.nodes[0].next = &a.nodes[1];
    clear(&a);
    sx_check_qcp(NULL, 3, NULL, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    CHECK(r.witness_length == 3);
    sx_result_clear(&r);
    sx_check_qcp(NULL, SIZE_MAX, NULL, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_SIZE_OVERFLOW);
    no_output(&r);
    sx_result_clear(&r);
    /* Zero limits select finite defaults and allow the ordinary one-pivot case. */
    a = input(1, 1, simple);
    limit = (SxSolverLimits){0};
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    sx_result_clear(&r);
    clear(&a);
    /* Empty-input witness publication is included in the space budget. */
    limit = (SxSolverLimits){0};
    limit.max_milliseconds = ULLONG_MAX;
    sx_check_qcp(NULL, 0, &limit, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    sx_result_clear(&r);
    sx_check_qcp(NULL, 20, NULL, &r);
    good(&r, SX_Q_FEASIBLE, SX_Z_SAT);
    size_t peak = r.stats.peak_bytes;
    sx_result_clear(&r);
    limit = (SxSolverLimits){0};
    limit.max_table_bytes = peak - 1;
    sx_check_qcp(NULL, 20, &limit, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_SPACE);
    no_output(&r);
    sx_result_clear(&r);
    /* Cooperative timeout during a deliberately allocation-heavy creation/check. */
    size_t rows = 1000, vars = 20, count = rows * (vars + 1);
    const char **zeros = calloc(count, sizeof(*zeros));
    CHECK(zeros);
    for (size_t i = 0; i < count; i++)
        zeros[i] = "0";
    a = input(rows, vars, zeros);
    free(zeros);
    limit = (SxSolverLimits){0};
    limit.max_milliseconds = 1;
    sx_check_qcp(a.nodes, a.p.variables, &limit, &r);
    good(&r, SX_Q_UNKNOWN, SX_Z_UNKNOWN);
    CHECK(r.reason == SX_REASON_TIME && r.diagnostic == SX_D_TIME);
    no_output(&r);
    sx_result_clear(&r);
    clear(&a);
    CHECK(sx_runtime_live_bytes() == 0 && sx_live_blocks() == 0);
    printf("P3 tests passed: %zu full-call individually injected failures; witness/evidence, "
           "budgets, pivot-boundary and cooperative-time checks\n",
           faults);
    return 0;
}
