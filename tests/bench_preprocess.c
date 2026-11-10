#define _POSIX_C_SOURCE 200809L
#include "sx_solver_contract.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};
static void set(SxRat *q, int n) {
    char s[40];
    snprintf(s, sizeof(s), "%d", n);
    if (sx_rat_set(q, s, "1", NULL, NULL))
        exit(2);
}
static int cmp(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}
static double elapsed(const struct timespec *a, const struct timespec *b) {
    return (double)(b->tv_sec - a->tv_sec) * 1e9 + (double)(b->tv_nsec - a->tv_nsec);
}
int main(int argc, char **argv) {
    if (argc != 4)
        return 2;
    int sparse = !strcmp(argv[1], "sparse");
    unsigned flags = (unsigned)strtoul(argv[2], NULL, 10);
    size_t repeat = (size_t)strtoul(argv[3], NULL, 10);
    if (!repeat || flags > SX_OPT_ALL)
        return 2;
    size_t m = sparse ? 18 : 10, n = sparse ? 12 : 6, count = m * (n + 1);
    SxRat *owner = calloc(count, sizeof(*owner));
    __mpz_struct *view = calloc(count, sizeof(*view));
    struct InequList *nodes = calloc(m, sizeof(*nodes));
    double *times = calloc(repeat, sizeof(*times));
    if (!owner || !view || !nodes || !times)
        return 2;
    for (size_t k = 0; k < count; k++)
        sx_rat_init(&owner[k]);
    SxRat factor;
    sx_rat_init(&factor);
    if (sx_rat_set(&factor, "18446744073709551616", "1", NULL, NULL))
        return 2;
    for (size_t i = 0; i < m; i++) {
        if (sparse) {
            if (i < 12)
                set(&owner[i * (n + 1)], -(int)i - 1);
            else {
                size_t v = (i - 12) / 2;
                int sign = i % 2 ? -1 : 1;
                set(&owner[i * (n + 1)], sign * (int)(v + 1));
                set(&owner[i * (n + 1) + 2 * v + 1], -sign);
                for (size_t j = 0; j <= n; j++)
                    if (sx_rat_op(&owner[i * (n + 1) + j], '*', &owner[i * (n + 1) + j], &factor,
                                  NULL, NULL))
                        return 2;
            }
        } else {
            set(&owner[i * (n + 1)], -1);
            for (size_t j = 0; j < n; j++) {
                int a = (int)((i * 7 + j * 11) % 17) - 8;
                if (!a)
                    a = 1;
                set(&owner[i * (n + 1) + j + 1], a);
            }
        }
        nodes[i].coef = view + i * (n + 1);
        nodes[i].next = i + 1 < m ? &nodes[i + 1] : NULL;
    }
    for (size_t k = 0; k < count; k++)
        view[k] = owner[k].num;
    SxSolverLimits l = {0};
    l.disable_optimizations = flags;
    SxResult result;
    sx_result_init(&result);
    /* Warmup is outside timings. Input conversion and result clear are excluded. */
    sx_check_qcp(nodes, n, &l, &result);
    if (result.error || result.rational_status != SX_Q_FEASIBLE)
        return 3;
    sx_result_clear(&result);
    double mean = 0;
    for (size_t i = 0; i < repeat; i++) {
        struct timespec start, end;
        if (clock_gettime(CLOCK_MONOTONIC, &start))
            return 2;
        sx_check_qcp(nodes, n, &l, &result);
        if (clock_gettime(CLOCK_MONOTONIC, &end))
            return 2;
        if (result.error || result.rational_status != SX_Q_FEASIBLE ||
            result.integer_status != SX_Z_SAT)
            return 3;
        times[i] = elapsed(&start, &end);
        mean += times[i];
        if (i + 1 < repeat)
            sx_result_clear(&result);
    }
    qsort(times, repeat, sizeof(*times), cmp);
    double median =
        repeat % 2 ? times[repeat / 2] : (times[repeat / 2 - 1] + times[repeat / 2]) / 2;
    const SxSolverStats *s = &result.stats;
    printf("{\"case\":\"%s\",\"disable_opts\":%u,\"entry\":\"%s\",\"repeats\":%zu,\"mean_ns\":%.0f,"
           "\"median_ns\":%.0f,\"min_ns\":%.0f,\"max_ns\":%.0f,\"rows\":%zu,\"variables\":%zu,"
           "\"active_rows\":%zu,\"active_variables\":%zu,\"input_nonzeros\":%zu,\"input_cells\":%"
           "zu,\"active_nonzeros\":%zu,\"active_cells\":%zu,\"pivots\":%zu,\"allocations\":%zu,\"peak_bytes\":%"
           "zu,"
           "\"preprocess_coefficients_scanned\":%zu,\"verification_coefficients_skipped\":%zu}\n",
           argv[1], flags, "qcp", repeat, mean / (double)repeat, median, times[0],
           times[repeat - 1], m, n, s->active_rows, s->active_variables, s->input_nonzeros,
           s->input_cells, s->active_nonzeros, s->active_cells, s->pivots, s->allocations, s->peak_bytes,
           s->preprocess_coefficients_scanned,
           s->verification_coefficients_skipped);
    sx_result_clear(&result);
    for (size_t k = 0; k < count; k++)
        sx_rat_clear(&owner[k]);
    sx_rat_clear(&factor);
    free(owner);
    free(view);
    free(nodes);
    free(times);
    return sx_runtime_live_bytes() ? 4 : 0;
}
