#include "sx_table.h"
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "FAIL %d: %s\n", __LINE__, #x);                                        \
            exit(1);                                                                               \
        }                                                                                          \
    } while (0)
static void eq(const SxRat *q, const char *expect) {
    char *s = NULL;
    CHECK(q != NULL);
    CHECK(sx_rat_string(&s, q, NULL, NULL) == SX_OK);
    if (strcmp(s, expect))
        fprintf(stderr, "got %s expected %s\n", s, expect);
    CHECK(!strcmp(s, expect));
    sx_string_free(s);
}
static void set(SxRat *q, const char *n, const char *d) {
    CHECK(sx_rat_set(q, n, d, NULL, NULL) == SX_OK);
}
static SxTable *small(void) {
    unsigned int v[2] = {1, 1};
    __mpz_struct a[2] = {{0, 1, &v[0]}, {0, -1, &v[1]}};
    SxProblem p = {1, 1, a};
    SxTable *t = NULL;
    CHECK(sx_table_create(&t, &p, NULL, NULL) == SX_OK);
    return t;
}
static size_t failures;
static void fault_create(void) {
    unsigned int v[2] = {1, 1};
    __mpz_struct a[2] = {{0, 1, &v[0]}, {0, -1, &v[1]}};
    SxProblem p = {1, 1, a};
    SxTable *t = NULL;
    SxTableStats s;
    size_t baseline = sx_runtime_live_bytes();
    CHECK(sx_table_create(&t, &p, NULL, &s) == SX_OK);
    size_t count = s.allocations, peak = s.peak_table_bytes;
    sx_table_destroy(t);
    CHECK(sx_runtime_live_bytes() == baseline);
    for (size_t k = 1; k <= count; k++) {
        t = NULL;
        SxTableLimits l = {0};
        l.fail_at = k;
        CHECK(sx_table_create(&t, &p, &l, &s) == SX_OOM);
        CHECK(t == NULL && s.reason == SX_T_ALLOC);
        CHECK(sx_runtime_live_bytes() == baseline);
        failures++;
    }
    SxTableLimits l = {0};
    l.max_table_bytes = peak;
    t = NULL;
    CHECK(sx_table_create(&t, &p, &l, &s) == SX_OK);
    sx_table_destroy(t);
    t = NULL;
    l.max_table_bytes = peak - 1;
    CHECK(sx_table_create(&t, &p, &l, &s) == SX_LIMIT);
    CHECK(s.reason == SX_T_TOTAL_BYTES && t == NULL);
    CHECK(sx_runtime_live_bytes() == baseline);
}
static void fault_mutation(int mode) {
    SxRat lo, hi, x;
    sx_rat_init(&lo);
    sx_rat_init(&hi);
    sx_rat_init(&x);
    set(&lo, "-2", "1");
    set(&hi, "3", "1");
    set(&x, "1", "3");
    SxTable *t = small();
    SxTableStats s;
    SxError e;
    if (mode == 0)
        e = sx_table_pivot(&t, 0, 0, 0, NULL, &s);
    else if (mode == 1)
        e = sx_table_bounds(&t, 0, &lo, &hi, NULL, &s);
    else if (mode == 2)
        e = sx_table_move(&t, 0, &x, NULL, &s);
    else
        e = sx_table_recompute(&t, NULL, &s);
    CHECK(e == SX_OK);
    size_t count = s.allocations, peak = s.peak_table_bytes;
    sx_table_destroy(t);
    for (size_t k = 1; k <= count; k++) {
        t = small();
        SxTable *old = t;
        size_t baseline = sx_runtime_live_bytes();
        SxTableLimits l = {0};
        l.fail_at = k;
        if (mode == 0)
            e = sx_table_pivot(&t, 0, 0, 0, &l, &s);
        else if (mode == 1)
            e = sx_table_bounds(&t, 0, &lo, &hi, &l, &s);
        else if (mode == 2)
            e = sx_table_move(&t, 0, &x, &l, &s);
        else
            e = sx_table_recompute(&t, &l, &s);
        CHECK(e == SX_OOM && s.reason == SX_T_ALLOC);
        CHECK(t == old && sx_runtime_live_bytes() == baseline);
        eq(sx_table_value(t, 0), "0/1");
        eq(sx_table_value(t, 1), "1/1");
        CHECK(sx_table_check(t, NULL, NULL) == SX_OK);
        sx_table_destroy(t);
        failures++;
    }
    t = small();
    SxTableLimits l = {0};
    l.max_table_bytes = peak;
    if (mode == 0)
        e = sx_table_pivot(&t, 0, 0, 0, &l, &s);
    else if (mode == 1)
        e = sx_table_bounds(&t, 0, &lo, &hi, &l, &s);
    else if (mode == 2)
        e = sx_table_move(&t, 0, &x, &l, &s);
    else
        e = sx_table_recompute(&t, &l, &s);
    CHECK(e == SX_OK);
    sx_table_destroy(t);
    t = small();
    SxTable *old = t;
    l.max_table_bytes = peak - 1;
    if (mode == 0)
        e = sx_table_pivot(&t, 0, 0, 0, &l, &s);
    else if (mode == 1)
        e = sx_table_bounds(&t, 0, &lo, &hi, &l, &s);
    else if (mode == 2)
        e = sx_table_move(&t, 0, &x, &l, &s);
    else
        e = sx_table_recompute(&t, &l, &s);
    CHECK(e == SX_LIMIT && s.reason == SX_T_TOTAL_BYTES && t == old);
    sx_table_destroy(t);
    sx_rat_clear(&lo);
    sx_rat_clear(&hi);
    sx_rat_clear(&x);
}
static void check_faults(void) {
    SxTable *t = small();
    SxTableStats s;
    CHECK(sx_table_check(t, NULL, &s) == SX_OK);
    size_t n = s.allocations, baseline = sx_runtime_live_bytes();
    for (size_t k = 1; k <= n; k++) {
        SxTableLimits l = {0};
        l.fail_at = k;
        CHECK(sx_table_check(t, &l, &s) == SX_OOM);
        CHECK(s.reason == SX_T_ALLOC && sx_runtime_live_bytes() == baseline);
        failures++;
    }
    sx_table_destroy(t);
}
static void import_tests(void) {
    SxRat a, b;
    sx_rat_init(&a);
    sx_rat_init(&b);
    set(&a, "-18446744073709551616", "3");
    CHECK(sx_rat_import(&b, &a.num, NULL, NULL) == SX_OK);
    eq(&b, "-18446744073709551616/1");
    CHECK(sx_rat_import(&a, &a.num, NULL, NULL) == SX_OK);
    eq(&a, "-18446744073709551616/1");
    SxStats s;
    CHECK(sx_rat_import(&b, &a.num, NULL, &s) == SX_OK);
    size_t count = s.allocations;
    for (size_t k = 1; k <= count; k++) {
        set(&b, "17", "19");
        size_t bytes = sx_runtime_live_bytes();
        SxLimits l = {0, 0, k};
        CHECK(sx_rat_import(&b, &a.num, &l, &s) == SX_OOM);
        eq(&b, "17/19");
        CHECK(sx_runtime_live_bytes() == bytes);
        failures++;
    }
    SxLimits bad = {3, 0, 0};
    CHECK(sx_rat_import(&b, &a.num, &bad, &s) == SX_INVALID && s.reason == SX_AR_BAD_ARGUMENT);
    sx_rat_clear(&a);
    sx_rat_clear(&b);
}
int main(void) {
    size_t initial = sx_runtime_live_bytes();
    /* s=1-x-y, z=2+3x-y. Negative pivot x makes x=1-s-y,
       z=5-3s-4y; fixing z then y transfers the violation. */
    unsigned int v[] = {1, 1, 1, 2, 3, 1};
    __mpz_struct a[] = {{0, 1, v},     {0, -1, v + 1}, {0, -1, v + 2},
                        {0, 1, v + 3}, {0, 1, v + 4},  {0, -1, v + 5}};
    __mpz_struct saved[6];
    memcpy(saved, a, sizeof a);
    unsigned int limbs[6];
    memcpy(limbs, v, sizeof v);
    SxProblem p = {2, 2, a};
    SxTable *t = NULL;
    SxTableStats st;
    CHECK(sx_table_create(&t, &p, NULL, &st) == SX_OK);
    CHECK(st.retained_table_bytes == sx_table_bytes(t));
    eq(sx_table_value(t, 2), "1/1");
    CHECK(!sx_table_lower(t, 0) && !sx_table_upper(t, 0));
    CHECK(sx_table_pivot(&t, 0, 0, 0, NULL, &st) == SX_OK);
    eq(sx_table_beta(t, 0), "1/1");
    eq(sx_table_coefficient(t, 0, 2), "-1/1");
    eq(sx_table_beta(t, 1), "5/1");
    eq(sx_table_coefficient(t, 1, 2), "-3/1");
    eq(sx_table_coefficient(t, 1, 1), "-4/1");
    eq(sx_table_value(t, 0), "1/1");
    eq(sx_table_value(t, 3), "5/1");
    CHECK(sx_table_pivot(&t, 1, 1, 0, NULL, NULL) == SX_OK);
    eq(sx_table_value(t, 1), "5/4");
    eq(sx_table_value(t, 0), "-1/4");
    CHECK(sx_table_check(t, NULL, NULL) == SX_OK);
    CHECK(sx_table_recompute(&t, NULL, NULL) == SX_OK);
    eq(sx_table_value(t, 0), "-1/4");
    CHECK(!memcmp(a, saved, sizeof a) && !memcmp(v, limbs, sizeof v));
    sx_table_destroy(t);
    /* Newly basic variable can exceed its own upper bound (full delta too far). */
    t = small();
    SxRat lo, hi;
    sx_rat_init(&lo);
    sx_rat_init(&hi);
    set(&hi, "1", "4");
    CHECK(sx_table_bounds(&t, 0, NULL, &hi, NULL, NULL) == SX_OK);
    CHECK(sx_table_pivot(&t, 0, 0, 0, NULL, NULL) == SX_OK);
    eq(sx_table_value(t, 0), "1/1");
    CHECK(sx_table_check(t, NULL, NULL) == SX_OK);
    SxTable *old = t;
    CHECK(sx_table_bounds(&t, 1, &hi, NULL, NULL, NULL) == SX_INVALID && t == old);
    sx_table_destroy(t);
    /* Lower violation with positive pivot and absent bounds. */
    t = small();
    set(&lo, "3", "1");
    CHECK(sx_table_bounds(&t, 1, &lo, NULL, NULL, NULL) == SX_OK);
    CHECK(sx_table_pivot(&t, 0, 0, 1, NULL, NULL) == SX_OK);
    eq(sx_table_value(t, 0), "-2/1");
    CHECK(!sx_table_upper(t, 1));
    sx_table_destroy(t);
    /* Positive pivot, both violated lower and violated upper. */
    {
        unsigned int vpos[] = {1, 2};
        __mpz_struct ipos[] = {{0, 1, vpos}, {0, 1, vpos + 1}};
        SxProblem pp = {1, 1, ipos};
        t = NULL;
        CHECK(sx_table_create(&t, &pp, NULL, NULL) == SX_OK);
        CHECK(sx_table_pivot(&t, 0, 0, 0, NULL, NULL) == SX_OK);
        eq(sx_table_value(t, 0), "-1/2");
        sx_table_destroy(t);
        t = NULL;
        CHECK(sx_table_create(&t, &pp, NULL, NULL) == SX_OK);
        CHECK(sx_table_bounds(&t, 1, &lo, NULL, NULL, NULL) == SX_OK);
        CHECK(sx_table_pivot(&t, 0, 0, 1, NULL, NULL) == SX_OK);
        eq(sx_table_value(t, 0), "1/1");
        sx_table_destroy(t);
    }
    /* QCP NULL and cycles are independent of capacities. */
    struct InequList second = {a + 3, NULL}, first = {a, &second};
    t = NULL;
    CHECK(sx_table_create_qcp(&t, &first, 2, NULL, NULL) == SX_OK);
    sx_table_destroy(t);
    second.next = &first;
    t = NULL;
    CHECK(sx_table_create_qcp(&t, &first, 2, NULL, &st) == SX_INVALID && st.reason == SX_T_CYCLE);
    second.next = NULL;
    first.coef = NULL;
    CHECK(sx_table_create_qcp(&t, &first, 2, NULL, &st) == SX_INVALID && t == NULL);
    first.coef = a;
    SxProblem empty = {0, 0, NULL};
    CHECK(sx_table_create(&t, &empty, NULL, NULL) == SX_OK);
    CHECK(sx_table_check(t, NULL, NULL) == SX_OK);
    CHECK(sx_table_recompute(&t, NULL, NULL) == SX_OK);
    sx_table_destroy(t);
    t = NULL;
    CHECK(sx_table_create_qcp(&t, NULL, 9, NULL, NULL) == SX_OK);
    CHECK(sx_table_variables(t) == 9);
    sx_table_destroy(t);
    t = NULL;
    SxProblem constants = {2, 0, a};
    CHECK(sx_table_create(&t, &constants, NULL, NULL) == SX_OK);
    CHECK(sx_table_rows(t) == 2 && sx_table_original_variables(t) == 0);
    CHECK(sx_table_pivot(&t, 0, 0, 0, NULL, NULL) == SX_INVALID);
    sx_table_destroy(t);
    {
        SxTableLimits invalid = {0};
        invalid.arithmetic.max_limbs = 3;
        t = NULL;
        CHECK(sx_table_create(&t, &empty, &invalid, &st) == SX_INVALID &&
              st.reason == SX_T_ARGUMENT);
        invalid.arithmetic.max_limbs = 0;
        invalid.arithmetic.fail_at = 1;
        CHECK(sx_table_create(&t, &empty, &invalid, &st) == SX_INVALID &&
              st.reason == SX_T_ARGUMENT);
    }
    /* Dynamic dimensions beyond old 8/16 and >64 bit exact import. */
    SxRat numbers[180];
    __mpz_struct big[180];
    for (size_t i = 0; i < 180; i++) {
        sx_rat_init(&numbers[i]);
        set(&numbers[i], i % 10 ? "-18446744073709551617" : "4294967296", "1");
        big[i] = numbers[i].num;
    }
    p = (SxProblem){18, 9, big};
    t = NULL;
    CHECK(sx_table_create(&t, &p, NULL, NULL) == SX_OK);
    eq(sx_table_coefficient(t, 0, 0), "-18446744073709551617/1");
    eq(sx_table_beta(t, 0), "4294967296/1");
    CHECK(sx_table_check(t, NULL, NULL) == SX_OK);
    sx_table_destroy(t);
    for (size_t i = 0; i < 180; i++)
        sx_rat_clear(&numbers[i]);
    unsigned int z = 0;
    __mpz_struct bad = {0, 1, &z};
    p = (SxProblem){1, 0, &bad};
    t = NULL;
    CHECK(sx_table_create(&t, &p, NULL, &st) == SX_INVALID && st.reason == SX_T_OBJECT);
    bad._mp_size = INT_MIN;
    CHECK(sx_table_create(&t, &p, NULL, &st) == SX_INVALID);
    bad = (__mpz_struct){1, 2, v};
    CHECK(sx_table_create(&t, &p, NULL, &st) == SX_INVALID);
    p = (SxProblem){SIZE_MAX, 2, a};
    CHECK(sx_table_create(&t, &p, NULL, &st) == SX_LIMIT && st.reason == SX_T_OVERFLOW);
    p = (SxProblem){0, SIZE_MAX, NULL};
    CHECK(sx_table_create(&t, &p, NULL, &st) == SX_LIMIT);
    t = small();
    SxTableLimits limits = {0};
    limits.arithmetic.max_bytes = 1;
    old = t;
    CHECK(sx_table_recompute(&t, &limits, &st) == SX_LIMIT && st.reason == SX_T_ARITH_BYTES &&
          t == old);
    limits = (SxTableLimits){0};
    limits.arithmetic.max_limbs = 4;
    SxRat huge;
    sx_rat_init(&huge);
    set(&huge, "340282366920938463463374607431768211456", "1");
    CHECK(sx_table_bounds(&t, 1, &huge, NULL, &limits, &st) == SX_LIMIT && st.reason == SX_T_LIMBS);
    sx_rat_clear(&huge);
    sx_table_destroy(t);
    sx_rat_clear(&lo);
    sx_rat_clear(&hi);
    CHECK(sx_runtime_live_bytes() == initial);
    import_tests();
    fault_create();
    for (int i = 0; i < 4; i++)
        fault_mutation(i);
    check_faults();
    CHECK(sx_runtime_live_bytes() == initial && sx_live_blocks() == 0);
    printf("P2 tests passed: %zu individually injected allocation failures; total-budget "
           "exact/one-byte-below checks and no live owned bytes\n",
           failures);
    return 0;
}
