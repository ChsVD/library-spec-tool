/* Demonstrates the original QCP data format, not linking a second MiniGMP.
 * Borrowed integer headers are never cleared: their owners are SxRat objects.
 * Include only this project's public header in this translation unit. */
#include "sx_solver_contract.h"
#include <stdio.h>
#include <string.h>

/* Exact original FME layout. If the application's TU already defines this tag,
 * use that definition there; do not include two copies of MiniGMP typedefs. */
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};

static const char *reason(SxReason value) {
    switch (value) {
    case SX_REASON_NONE:
        return "NONE";
    case SX_REASON_FRACTIONAL:
        return "FRACTIONAL";
    case SX_REASON_SPACE:
        return "SPACE";
    case SX_REASON_ARITH_SPACE:
        return "ARITH_SPACE";
    case SX_REASON_LIMBS:
        return "LIMBS";
    case SX_REASON_SIZE_OVERFLOW:
        return "SIZE_OVERFLOW";
    case SX_REASON_PIVOTS:
        return "PIVOTS";
    case SX_REASON_TIME:
        return "TIME";
    case SX_REASON_CONFLICT:
        return "CONFLICT";
    case SX_REASON_INVALID_INPUT:
        return "INVALID_INPUT";
    case SX_REASON_ALLOCATION:
        return "ALLOCATION";
    case SX_REASON_INTERNAL:
        return "INTERNAL";
    }
    return "INVALID_REASON";
}
static int report(const SxResult *result) {
    /* Runtime errors are NOT mathematical UNSAT or resource UNKNOWN. */
    switch (result->error) {
    case SX_OK:
        break;
    case SX_INVALID:
        fprintf(stderr, "invalid input/configuration, diagnostic=%d\n", (int)result->diagnostic);
        return 1;
    case SX_OOM:
        fprintf(stderr, "allocation failed, no mathematical conclusion\n");
        return 1;
    case SX_INTERNAL:
        fprintf(stderr, "internal/clock error, diagnostic=%d\n", (int)result->diagnostic);
        return 1;
    case SX_LIMIT:
        fprintf(stderr, "unexpected public LIMIT (contract violation)\n");
        return 1;
    }
    switch (result->rational_status) {
    case SX_Q_FEASIBLE:
        puts("Q=FEASIBLE: verified against every original input row");
        break;
    case SX_Q_UNSAT:
        puts("Q=UNSAT: verified local blocking-row contradiction");
        break;
    case SX_Q_UNKNOWN:
        printf("Q=UNKNOWN: resource reason=%s; retry from original input\n",
               reason(result->reason));
        break;
    case SX_Q_NOT_RUN:
        fprintf(stderr, "unexpected NOT_RUN without runtime error\n");
        return 1;
    }
    switch (result->integer_status) {
    case SX_Z_SAT:
        puts("Z=SAT: the verified witness is integral");
        break;
    case SX_Z_UNSAT:
        puts("Z=UNSAT: follows from rational infeasibility");
        break;
    case SX_Z_UNKNOWN:
        if (result->reason == SX_REASON_FRACTIONAL)
            puts("Z=UNKNOWN: FRACTIONAL (this witness does not exclude integer solutions)");
        else
            printf("Z=UNKNOWN: resource reason=%s; no integer decision\n", reason(result->reason));
        break;
    case SX_Z_NOT_DECIDED:
        fprintf(stderr, "unexpected NOT_DECIDED without runtime error\n");
        return 1;
    }
    for (size_t i = 0; i < result->witness_length; i++) {
        char *text = NULL;
        if (sx_rat_string(&text, &result->witness[i], NULL, NULL) != SX_OK) {
            fprintf(stderr, "cannot format witness\n");
            return 1;
        }
        printf("x%zu=%s\n", i, text);
        sx_string_free(text);
    }
    if (result->conflict.present)
        printf("conflict source row=%zu, blockers=%zu\n", result->conflict.bound_source_row,
               result->conflict.blocker_count);
    return 0;
}
int main(int argc, char **argv) {
    if (argc > 2) {
        fputs("usage: qcp_example [integer|fraction|conflict|budget]\n", stderr);
        return 2;
    }
    const char *mode = argc == 2 ? argv[1] : "integer";
    /* Rows are [constant,x0,...], relation constant+sum coefficient*x<=0. */
    const char *integer[] = {"1", "-1", "-1", "1"};  /* x=1 */
    const char *fraction[] = {"1", "-2", "-1", "2"}; /* 2*x=1 */
    const char *conflict[] = {"1", "-1", "0", "1"};  /* x>=1, x<=0 */
    const char *budget[] = {"-3", "1", "1", "3", "-1", "-1", "-1", "1", "-1", "1", "-1", "1"};
    const char **values = integer;
    size_t rows = 2, variables = 1;
    SxSolverLimits limits = {0}; /* New header + matching library; initialize ALL fields. */
    if (!strcmp(mode, "fraction"))
        values = fraction;
    else if (!strcmp(mode, "conflict"))
        values = conflict;
    else if (!strcmp(mode, "budget")) {
        values = budget;
        rows = 4;
        variables = 2;
        limits.max_pivots = 1;
    } else if (strcmp(mode, "integer")) {
        fprintf(stderr, "usage: qcp_example [integer|fraction|conflict|budget]\n");
        return 2;
    }
    SxRat owners[12];
    __mpz_struct coefficients[12];
    struct InequList nodes[4];
    size_t initialized = 0, count = rows * (variables + 1);
    int rc = 1;
    SxResult result;
    sx_result_init(&result);
    for (size_t i = 0; i < count; i++) {
        sx_rat_init(&owners[i]);
        initialized++;
        /* Safe project integer construction: no raw mpz allocator, no system GMP.
         * num is integral because denominator is exactly one. */
        SxError e = sx_rat_set(&owners[i], values[i], "1", NULL, NULL);
        if (e != SX_OK) {
            fprintf(stderr, "input construction failed, error=%d\n", (int)e);
            goto done;
        }
        coefficients[i] = owners[i].num; /* NON-OWNING read-only integer header view. */
    }
    for (size_t i = 0; i < rows; i++) {
        nodes[i].coef = coefficients + i * (variables + 1);
        nodes[i].next = i + 1 < rows ? &nodes[i + 1] : NULL;
    }
    /* nodes, headers and owners stay valid throughout this synchronous call.
     * Solver copies what it owns; it never frees nodes/coefficients/owners. */
    sx_check_qcp(nodes, variables, &limits, &result);
    /* Deliberately destroy all caller-owned input BEFORE reading the result. */
    for (size_t i = 0; i < initialized; i++)
        sx_rat_clear(&owners[i]);
    initialized = 0;
    rc = report(&result);
done:
    for (size_t i = 0; i < initialized; i++)
        sx_rat_clear(&owners[i]);
    /* Never mpz_clear(coefficients[i]): those headers only borrowed owners[i].num. */
    sx_result_clear(&result);
    sx_result_clear(&result); /* Idempotent. */
    return rc;
}
