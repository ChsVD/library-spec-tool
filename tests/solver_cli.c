#include "sx_solver_contract.h"
#include <ctype.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum { TOKEN_OK, TOKEN_EOF, TOKEN_INVALID, TOKEN_OOM, TOKEN_IO } TokenStatus;
static TokenStatus token(char **out) {
    *out = NULL;
    size_t n = 0, cap = 64;
    char *s = malloc(cap);
    if (!s)
        return TOKEN_OOM;
    int c;
    do {
        c = getchar();
    } while (c != EOF && isspace((unsigned char)c));
    if (c == EOF) {
        free(s);
        return ferror(stdin) ? TOKEN_IO : TOKEN_EOF;
    }
    do {
        if (c == 0) {
            free(s);
            return TOKEN_INVALID;
        }
        if (n + 1 == cap) {
            if (cap > SIZE_MAX / 2) {
                free(s);
                return TOKEN_OOM;
            }
            cap *= 2;
            char *t = realloc(s, cap);
            if (!t) {
                free(s);
                return TOKEN_OOM;
            }
            s = t;
        }
        s[n++] = (char)c;
        c = getchar();
    } while (c != EOF && !isspace((unsigned char)c));
    if (c == EOF && ferror(stdin)) {
        free(s);
        return TOKEN_IO;
    }
    s[n] = 0;
    *out = s;
    return TOKEN_OK;
}
static int natural(const char *s, unsigned long long *out) {
    if (!s || !*s || *s == '-')
        return 0;
    errno = 0;
    char *end;
    unsigned long long n = strtoull(s, &end, 10);
    if (errno || *end)
        return 0;
    *out = n;
    return 1;
}
static void rat(const SxRat *q) {
    char *s = NULL;
    if (sx_rat_string(&s, q, NULL, NULL) != SX_OK) {
        fputs("cannot render rational\n", stderr);
        exit(2);
    }
    printf("\"%s\"", s);
    sx_string_free(s);
}
static const char *error(SxError e) {
    const char *names[] = {"OK", "INVALID", "OOM", "LIMIT", "INTERNAL"};
    return names[e];
}
static const char *reason(SxReason e) {
    const char *names[] = {"NONE",          "FRACTIONAL", "SPACE",    "LIMBS",
                           "PIVOTS",        "TIME",       "CONFLICT", "ARITH_SPACE",
                           "INVALID_INPUT", "ALLOCATION", "INTERNAL", "SIZE_OVERFLOW"};
    return names[e];
}
static const char *diagnostic(SxDiagnostic e) {
    const char *names[] = {"NONE",        "ARGUMENT", "DIMENSION", "OBJECT",   "TOTAL_BYTES",
                           "ARITH_BYTES", "LIMBS",    "PIVOTS",    "TIME",     "ALLOC",
                           "INVARIANT",   "REENTRY",  "CLOCK",     "OVERFLOW", "CYCLE"};
    return names[e];
}
static void print_result(const SxResult *r) {
    const char *q[] = {"NOT_RUN", "FEASIBLE", "UNSAT", "UNKNOWN"},
               *z[] = {"NOT_DECIDED", "SAT", "UNSAT", "UNKNOWN"};
    printf("{\"error\":\"%s\",\"q\":\"%s\",\"z\":\"%s\",\"reason\":\"%s\",\"diagnostic\":\"%s\","
           "\"arithmetic_reason\":%d,\"witness\":[",
           error(r->error), q[r->rational_status], z[r->integer_status], reason(r->reason),
           diagnostic(r->diagnostic), (int)r->arithmetic_reason);
    for (size_t i = 0; i < r->witness_length; i++) {
        if (i)
            putchar(',');
        rat(&r->witness[i]);
    }
    printf("],\"stats\":{\"pivots\":%zu,\"allocations\":%zu,\"peak_bytes\":%zu,\"comparisons\":%zu,"
           "\"verified_rows\":%zu,\"conflict_terms\":%zu},\"conflict\":",
           r->stats.pivots, r->stats.allocations, r->stats.peak_bytes, r->stats.comparisons,
           r->stats.verified_rows, r->stats.conflict_terms);
    const SxConflict *c = &r->conflict;
    if (!c->present)
        fputs("null", stdout);
    else {
        printf("{\"row\":%zu,\"basic_variable\":%zu,\"bound_source_row\":", c->row,
               c->basic_variable);
        if (c->bound_source_row == SIZE_MAX)
            fputs("null", stdout);
        else
            printf("%zu", c->bound_source_row);
        printf(",\"to_lower\":%s,\"constant\":", c->to_lower ? "true" : "false");
        rat(&c->constant);
        fputs(",\"required\":", stdout);
        rat(&c->required);
        fputs(",\"attainable\":", stdout);
        rat(&c->attainable);
        fputs(",\"blockers\":[", stdout);
        for (size_t i = 0; i < c->blocker_count; i++) {
            const SxBlocker *b = &c->blockers[i];
            if (i)
                putchar(',');
            printf("{\"variable\":%zu,\"source_row\":", b->variable);
            if (b->source_row == SIZE_MAX)
                fputs("null", stdout);
            else
                printf("%zu", b->source_row);
            printf(",\"is_lower\":%s,\"coefficient\":", b->is_lower ? "true" : "false");
            rat(&b->coefficient);
            fputs(",\"bound\":", stdout);
            rat(&b->bound);
            putchar('}');
        }
        fputs("]}", stdout);
    }
    printf(
        ",\"optimization\":{\"input_rows\":%zu,\"input_variables\":%zu,\"active_rows\":%zu,"
        "\"active_variables\":%zu,\"input_nonzeros\":%zu,\"input_cells\":%zu,\"active_nonzeros\":%"
        "zu,\"active_cells\":%zu,\"dropped_true_rows\":%zu,\"removed_variables\":%zu,\"gcd_reduced_"
        "rows\":%zu,\"constant_conflicts\":%zu,\"preprocess_"
        "coefficients_scanned\":%zu,\"verification_coefficients_skipped\":%zu}}\n",
        r->stats.input_rows, r->stats.input_variables, r->stats.active_rows,
        r->stats.active_variables, r->stats.input_nonzeros, r->stats.input_cells,
        r->stats.active_nonzeros, r->stats.active_cells, r->stats.dropped_true_rows,
        r->stats.removed_variables, r->stats.gcd_reduced_rows, r->stats.constant_conflicts,
        r->stats.preprocess_coefficients_scanned, r->stats.verification_coefficients_skipped);
}
struct InequList { mpz_ptr coef; struct InequList *next; };
int main(int argc, char **argv) {
    SxSolverLimits limits = {0};
    for (int i = 1; i < argc; i += 2) {
        unsigned long long v;
        if (i + 1 >= argc || !natural(argv[i + 1], &v)) {
            fputs("option requires an unsigned integer\n", stderr);
            return 2;
        }
        if (!strcmp(argv[i], "--ms"))
            limits.max_milliseconds = v;
        else {
            if (v > SIZE_MAX)
                return 2;
            size_t x = (size_t)v;
            if (!strcmp(argv[i], "--disable-opts")) {
                if (x > SX_OPT_ALL)
                    return 2;
                limits.disable_optimizations = (unsigned int)x;
            } else if (!strcmp(argv[i], "--pivots"))
                limits.max_pivots = x;
            else if (!strcmp(argv[i], "--bytes"))
                limits.max_table_bytes = x;
            else if (!strcmp(argv[i], "--limbs"))
                limits.arithmetic.max_limbs = x;
            else if (!strcmp(argv[i], "--arith-bytes"))
                limits.arithmetic.max_bytes = x;
            else if (!strcmp(argv[i], "--fail-at"))
                limits.fail_at = x;
            else {
                fputs("unknown option\n", stderr);
                return 2;
            }
        }
    }
    char *s = NULL;
    TokenStatus ts = token(&s);
    unsigned long long m, n;
    if (ts != TOKEN_OK || !natural(s, &m)) {
        free(s);
        return 2;
    }
    free(s);
    ts = token(&s);
    if (ts != TOKEN_OK || !natural(s, &n)) {
        free(s);
        return 2;
    }
    free(s);
    if (m > SIZE_MAX || n >= SIZE_MAX)
        return 2;
    size_t rows = (size_t)m, vars = (size_t)n;
    if (rows > SIZE_MAX / (vars + 1))
        return 2;
    size_t count = rows * (vars + 1);
    if (count > SIZE_MAX / sizeof(SxRat) || count > SIZE_MAX / sizeof(__mpz_struct) ||
        rows > SIZE_MAX / sizeof(struct InequList))
        return 2;
    SxRat *storage = count ? calloc(count, sizeof(*storage)) : NULL;
    __mpz_struct *input = count ? calloc(count, sizeof(*input)) : NULL;
    if (count && (!storage || !input)) {
        free(storage);
        free(input);
        return 2;
    }
    struct InequList *nodes = rows ? calloc(rows, sizeof(*nodes)) : NULL;
    if (rows && !nodes) {
        free(storage);
        free(input);
        return 2;
    }
    for (size_t i = 0; i < rows; i++) {
        nodes[i].coef = input + i * (vars + 1);
        nodes[i].next = i + 1 < rows ? &nodes[i + 1] : NULL;
    }
    size_t initialized = 0;
    int rc = 2;
    for (size_t i = 0; i < count; i++) {
        sx_rat_init(&storage[i]);
        initialized++;
        ts = token(&s);
        if (ts != TOKEN_OK)
            goto done;
        SxError e = sx_rat_set(&storage[i], s, "1", NULL, NULL);
        free(s);
        if (e != SX_OK)
            goto done;
        input[i] = storage[i].num;
    }
    ts = token(&s);
    if (ts != TOKEN_EOF) {
        free(s);
        goto done;
    }
    {
        SxResult result;
        sx_result_init(&result);
        sx_check_qcp(nodes, vars, &limits, &result);
        print_result(&result);
        sx_result_clear(&result);
    }
    rc = 0;
done:
    for (size_t i = 0; i < initialized; i++)
        sx_rat_clear(&storage[i]);
    free(storage);
    free(input);
    free(nodes);
    if (sx_runtime_live_bytes())
        return 3;
    return rc;
}
