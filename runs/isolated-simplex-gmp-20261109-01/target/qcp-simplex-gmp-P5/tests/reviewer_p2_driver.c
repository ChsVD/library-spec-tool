/* Test adapter for reviewer_p2.py. The expected tableau is calculated in Python. */
#include "sx_table.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define REQUIRE(x) do { if (!(x)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x); exit(1); } } while (0)

static void emit_rat(const SxRat *q) {
    char *s = NULL;
    REQUIRE(q && sx_rat_string(&s, q, NULL, NULL) == SX_OK);
    printf("%s ", s);
    sx_string_free(s);
}

static void emit_state(const SxTable *t) {
    size_t m = sx_table_rows(t), total = sx_table_variables(t);
    REQUIRE(sx_table_check(t, NULL, NULL) == SX_OK);
    for (size_t r = 0; r < m; ++r) {
        size_t b = sx_table_basic(t, r);
        REQUIRE(sx_table_basic_row(t, b) == r && sx_table_nonbasic_column(t, b) == SIZE_MAX);
        printf("%zu ", b);
    }
    for (size_t col = 0; col < total-m; ++col) {
        size_t v = sx_table_nonbasic(t, col);
        REQUIRE(sx_table_nonbasic_column(t, v) == col && sx_table_basic_row(t, v) == SIZE_MAX);
    }
    for (size_t v = 0; v < total; ++v) emit_rat(sx_table_value(t, v));
    for (size_t r = 0; r < m; ++r) {
        emit_rat(sx_table_beta(t, r));
        for (size_t v = 0; v < total; ++v) emit_rat(sx_table_coefficient(t, r, v));
    }
    putchar('\n');
}

int main(void) {
    size_t m, n, moves;
    REQUIRE(scanf("%zu %zu", &m, &n) == 2 && m <= 32 && n <= 32);
    size_t count = m * (n+1);
    __mpz_struct *flat = calloc(count+1, sizeof(*flat));
    SxRat *owners = calloc(count+1, sizeof(*owners));
    REQUIRE(flat && owners);
    for (size_t i = 0; i < count; ++i) {
        char token[512];
        REQUIRE(scanf("%511s", token) == 1);
        sx_rat_init(&owners[i]);
        REQUIRE(sx_rat_set(&owners[i], token, "1", NULL, NULL) == SX_OK);
        flat[i] = owners[i].num; /* Read-only input view. Only owners owns limbs. */
    }
    SxProblem p = {m, n, count ? flat : NULL};
    SxTable *t = NULL;
    REQUIRE(sx_table_create(&t, &p, NULL, NULL) == SX_OK);
    REQUIRE(sx_table_original_variables(t) == n && sx_table_rows(t) == m);
    /* Deliberately release all source storage before inspecting the table. */
    for (size_t i = 0; i < count; ++i) sx_rat_clear(&owners[i]);
    free(owners);
    free(flat);
    for (size_t v = 0; v < n; ++v) {
        char lo[64], hi[64];
        REQUIRE(scanf("%63s %63s", lo, hi) == 2);
        SxRat a, b;
        sx_rat_init(&a);
        sx_rat_init(&b);
        int has_lo = strcmp(lo, "*") != 0, has_hi = strcmp(hi, "*") != 0;
        if (has_lo) REQUIRE(sx_rat_set(&a, lo, "1", NULL, NULL) == SX_OK);
        if (has_hi) REQUIRE(sx_rat_set(&b, hi, "1", NULL, NULL) == SX_OK);
        if (has_lo || has_hi) REQUIRE(sx_table_bounds(&t, v, has_lo ? &a : NULL, has_hi ? &b : NULL, NULL, NULL) == SX_OK);
        sx_rat_clear(&a);
        sx_rat_clear(&b);
    }
    emit_state(t);
    REQUIRE(scanf("%zu", &moves) == 1);
    for (size_t k = 0; k < moves; ++k) {
        size_t r, e;
        char side;
        REQUIRE(scanf("%zu %zu %c", &r, &e, &side) == 3);
        REQUIRE(sx_table_pivot(&t, r, e, side == 'L', NULL, NULL) == SX_OK);
        emit_state(t);
    }
    sx_table_destroy(t);
    REQUIRE(sx_live_blocks() == 0);
    return 0;
}
