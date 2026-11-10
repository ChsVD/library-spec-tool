#include "sx_arith.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #x);                                   \
            exit(1);                                                                               \
        }                                                                                          \
    } while (0)
static void eq(SxRat *q, const char *want) {
    char *s = NULL;
    CHECK(sx_rat_string(&s, q, NULL, NULL) == SX_OK);
    if (strcmp(s, want))
        fprintf(stderr, "got %s expected %s\n", s, want);
    CHECK(!strcmp(s, want));
    sx_string_free(s);
}
static void set(SxRat *q, const char *n, const char *d) {
    CHECK(sx_rat_set(q, n, d, NULL, NULL) == SX_OK);
}
static size_t injected;
/* Re-run a whole operation, failing each dynamic allocation including context.
   A separate expected value and retained operand verify atomic commit. */
static void faults(char op) {
    SxRat a, b, o;
    sx_rat_init(&a);
    sx_rat_init(&b);
    sx_rat_init(&o);
    set(&a, "18446744073709551616", "4294967296");
    set(&b, "-18446744073709551615", "79228162514264337593543950336");
    set(&o, "17", "19");
    SxStats st;
    CHECK(sx_rat_op(&o, op, &a, &b, NULL, &st) == SX_OK);
    size_t count = st.allocations;
    for (size_t k = 1; k <= count; k++) {
        set(&o, "17", "19");
        size_t blocks = sx_live_blocks();
        SxLimits l = {0, 0, k};
        CHECK(sx_rat_op(&o, op, &a, &b, &l, &st) == SX_OOM);
        CHECK(st.reason == SX_AR_ALLOC);
        CHECK(sx_live_blocks() == blocks);
        eq(&o, "17/19");
        eq(&a, "4294967296/1");
        ++injected;
    }
    for (size_t k = 1; k <= count; k++) {
        set(&a, "18446744073709551616", "4294967296");
        size_t blocks = sx_live_blocks();
        SxLimits l = {0, 0, k};
        CHECK(sx_rat_op(&a, op, &a, &b, &l, &st) == SX_OOM);
        CHECK(st.reason == SX_AR_ALLOC);
        CHECK(sx_live_blocks() == blocks);
        eq(&a, "4294967296/1");
        ++injected;
    }
    for (int mode = 0; mode < 2; mode++) {
        set(&a, "5", "7");
        set(&b, "11", "13");
        SxRat *target = mode ? &a : &b;
        CHECK(sx_rat_op(target, op, &a, mode ? &a : &b, NULL, &st) == SX_OK);
        size_t attempts = st.allocations;
        for (size_t k = 1; k <= attempts; k++) {
            set(&a, "5", "7");
            set(&b, "11", "13");
            size_t blocks = sx_live_blocks();
            SxLimits l = {0, 0, k};
            CHECK(sx_rat_op(target, op, &a, mode ? &a : &b, &l, &st) == SX_OOM);
            CHECK(st.reason == SX_AR_ALLOC);
            CHECK(sx_live_blocks() == blocks);
            eq(&a, "5/7");
            eq(&b, "11/13");
            injected++;
        }
    }
    sx_rat_clear(&a);
    sx_rat_clear(&b);
    sx_rat_clear(&o);
}
int main(void) {
    SxRat a, b, o;
    sx_rat_init(&a);
    sx_rat_init(&b);
    sx_rat_init(&o);
    eq(&o, "0/1");
    set(&a, "1", "2");
    eq(&a, "1/2");
    set(&a, "-0", "-123");
    eq(&a, "0/1");
    set(&a, "4294967295", "-4294967296");
    eq(&a, "-4294967295/4294967296");
    set(&a, "18446744073709551616", "4294967296");
    eq(&a, "4294967296/1");
    set(&b, "3", "7");
    for (const char *p = "+-*/"; *p; p++) {
        CHECK(sx_rat_op(&o, *p, &a, &b, NULL, NULL) == SX_OK);
        char *expected = NULL;
        CHECK(sx_rat_string(&expected, &o, NULL, NULL) == SX_OK);
        SxRat x, y;
        sx_rat_init(&x);
        sx_rat_init(&y);
        set(&x, "18446744073709551616", "4294967296");
        set(&y, "3", "7");
        CHECK(sx_rat_op(&x, *p, &x, &y, NULL, NULL) == SX_OK);
        eq(&x, expected);
        set(&x, "18446744073709551616", "4294967296");
        CHECK(sx_rat_op(&y, *p, &x, &y, NULL, NULL) == SX_OK);
        eq(&y, expected);
        sx_string_free(expected);
        sx_rat_clear(&x);
        sx_rat_clear(&y);
    }
    set(&a, "2", "3");
    CHECK(sx_rat_op(&a, '*', &a, &a, NULL, NULL) == SX_OK);
    eq(&a, "4/9");
    int c = 7;
    CHECK(sx_rat_cmp(&c, &a, &a, NULL, NULL) == SX_OK && c == 0);
    set(&o, "17", "19");
    CHECK(sx_rat_set(&o, "2x", "3", NULL, NULL) == SX_INVALID);
    eq(&o, "17/19");
    CHECK(sx_rat_set(&o, "1", "0", NULL, NULL) == SX_INVALID);
    eq(&o, "17/19");
    set(&b, "0", "1");
    CHECK(sx_rat_op(&o, '/', &a, &b, NULL, NULL) == SX_INVALID);
    eq(&o, "17/19");
    SxLimits tiny = {0, 1, 0};
    CHECK(sx_rat_op(&o, '+', &a, &b, &tiny, NULL) == SX_LIMIT);
    eq(&o, "17/19");
    SxLimits limbs = {4, 0, 0};
    CHECK(sx_rat_set(&o, "340282366920938463463374607431768211456", "1", &limbs, NULL) == SX_LIMIT);
    eq(&o, "17/19");
    SxStats diag;
    CHECK(sx_rat_set(&o, "x", "1", NULL, &diag) == SX_INVALID && diag.reason == SX_AR_BAD_DECIMAL);
    CHECK(sx_rat_set(&o, "1", "0", NULL, &diag) == SX_INVALID &&
          diag.reason == SX_AR_ZERO_DENOMINATOR);
    CHECK(sx_rat_op(&o, '/', &a, &b, NULL, &diag) == SX_INVALID && diag.reason == SX_AR_DIV_ZERO);
    CHECK(sx_rat_op(&o, '+', &a, &b, &tiny, &diag) == SX_LIMIT && diag.reason == SX_AR_BYTES);
    CHECK(sx_rat_set(&o, "340282366920938463463374607431768211456", "1", &limbs, &diag) ==
              SX_LIMIT &&
          diag.reason == SX_AR_LIMBS);
    CHECK(sx_rat_op(NULL, '+', &a, &b, NULL, &diag) == SX_INVALID &&
          diag.reason == SX_AR_BAD_ARGUMENT);
    SxLimits first = {0, 0, 1};
    CHECK(sx_rat_set(&o, "1", "1", &first, &diag) == SX_OOM && diag.reason == SX_AR_ALLOC &&
          diag.allocations == 1);
    SxStats st;
    CHECK(sx_rat_set(&o, "-79228162514264337593543950336", "18446744073709551616", NULL, &st) ==
          SX_OK);
    size_t count = st.allocations;
    for (size_t k = 1; k <= count; k++) {
        set(&o, "17", "19");
        size_t blocks = sx_live_blocks();
        SxLimits l = {0, 0, k};
        CHECK(sx_rat_set(&o, "-79228162514264337593543950336", "18446744073709551616", &l, &st) ==
              SX_OOM);
        CHECK(st.reason == SX_AR_ALLOC);
        CHECK(sx_live_blocks() == blocks);
        eq(&o, "17/19");
        injected++;
    }
    char *str = NULL;
    CHECK(sx_rat_string(&str, &o, NULL, &st) == SX_OK);
    sx_string_free(str);
    count = st.allocations;
    for (size_t k = 1; k <= count; k++) {
        size_t blocks = sx_live_blocks();
        str = NULL;
        SxLimits l = {0, 0, k};
        CHECK(sx_rat_string(&str, &o, &l, &st) == SX_OOM);
        CHECK(str == NULL && sx_live_blocks() == blocks);
        injected++;
    }
    CHECK(sx_rat_cmp(&c, &a, &o, NULL, &st) == SX_OK);
    count = st.allocations;
    for (size_t k = 1; k <= count; k++) {
        size_t blocks = sx_live_blocks();
        c = 42;
        SxLimits l = {0, 0, k};
        CHECK(sx_rat_cmp(&c, &a, &o, &l, &st) == SX_OOM);
        CHECK(c == 42 && sx_live_blocks() == blocks);
        injected++;
    }
    sx_rat_clear(&a);
    sx_rat_clear(&b);
    sx_rat_clear(&o);
    sx_rat_clear(&o);
    CHECK(sx_live_blocks() == 0);
    for (const char *p = "+-*/"; *p; p++)
        faults(*p);
    CHECK(sx_live_blocks() == 0);
    SxRat *many = malloc(100 * sizeof(*many));
    CHECK(many != NULL);
    for (size_t i = 0; i < 100; i++) {
        sx_rat_init(&many[i]);
        set(&many[i], "123456789123456789123456789", "987654321987654321");
    }
    for (size_t i = 0; i < 100; i++)
        sx_rat_clear(&many[i]);
    free(many);
    CHECK(sx_live_blocks() == 0);
    printf("C tests passed; %zu individually injected failures; no retained blocks\n", injected);
    return 0;
}
