#include "simplex.h"
#include <limits.h>

/* Independent implementation of the feasibility-tableau algorithm described
 * in Yices 2. No Yices source is copied. Not yet verified with QCP/Coq.
 * Arithmetic uses [-INT_MAX, INT_MAX], excluding INT_MIN to make negation safe.
 * Conservative overflow rejection is intentional and yields UNKNOWN only.
 */
static void rat_zero(struct SxRat *r) { r->num = 0; r->den = 1; }

static int positive_gcd(int a, int b) {
    while (b != 0) { int r = a % b; a = b; b = r; }
    return a;
}

static void rat_reduce(struct SxRat *r) {
    int n = r->num;
    int g;
    if (n < 0) n = -n;
    g = positive_gcd(n, r->den);
    r->num /= g;
    r->den /= g;
}

static int checked_mul(int x, int y, int *out) {
    int ax = x, ay = y;
    if (x == INT_MIN || y == INT_MIN) return 0;
    if (ax < 0) ax = -ax;
    if (ay < 0) ay = -ay;
    if (ay != 0 && ax > INT_MAX / ay) return 0;
    *out = x * y;
    return 1;
}

static int checked_add(int x, int y, int *out) {
    if (x == INT_MIN || y == INT_MIN) return 0;
    if (y > 0 && x > INT_MAX - y) return 0;
    if (y < 0 && x < -INT_MAX - y) return 0;
    *out = x + y;
    return 1;
}

static int rat_add(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out) {
    int p, q, n, d;
    if (!checked_mul(x->num, y->den, &p)) return 0;
    if (!checked_mul(y->num, x->den, &q)) return 0;
    if (!checked_add(p, q, &n)) return 0;
    if (!checked_mul(x->den, y->den, &d)) return 0;
    out->num = n; out->den = d;
    rat_reduce(out);
    return 1;
}

static int rat_mul(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out) {
    int n, d;
    if (!checked_mul(x->num, y->num, &n)) return 0;
    if (!checked_mul(x->den, y->den, &d)) return 0;
    out->num = n; out->den = d;
    rat_reduce(out);
    return 1;
}

static int rat_div(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out) {
    int n, d;
    if (y->num == 0) return 0;
    if (!checked_mul(x->num, y->den, &n)) return 0;
    if (!checked_mul(x->den, y->num, &d)) return 0;
    if (d < 0) { n = -n; d = -d; }
    out->num = n; out->den = d;
    rat_reduce(out);
    return 1;
}

static int rat_compare(const struct SxRat *x, const struct SxRat *y,
                       int *order) {
    int p, q;
    if (!checked_mul(x->num, y->den, &p)) return 0;
    if (!checked_mul(y->num, x->den, &q)) return 0;
    *order = 0;
    if (p < q) *order = -1;
    if (p > q) *order = 1;
    return 1;
}

int sx_recompute(struct SxState *s) {
    int i, j;
    struct SxRat sum, product;
    for (i = 0; i < s->rows; i++) {
        sum = s->rhs[i];
        for (j = 0; j < s->vars; j++) {
            if (!s->is_basic[j] && s->a[i][j].num != 0) {
                if (!rat_mul(&s->a[i][j], &s->value[j], &product)) return 0;
                if (!rat_add(&sum, &product, &sum)) return 0;
            }
        }
        s->value[s->basic[i]] = sum;
    }
    return 1;
}

int sx_initialize(struct SxState *s, int rows, int inputs,
                  const int c[SX_ROWS][SX_INPUT_VARS + 1]) {
    int i, j, b;
    if (rows < 0 || rows > SX_ROWS || inputs < 0 || inputs > SX_INPUT_VARS)
        return 0;
    for (i = 0; i < rows; i++)
        for (j = 0; j <= inputs; j++)
            if (c[i][j] == INT_MIN) return 0;
    s->rows = rows; s->inputs = inputs; s->vars = rows + inputs;
    for (j = 0; j < s->vars; j++) {
        s->is_basic[j] = 0;
        s->has_lower[j] = 0; s->has_upper[j] = 0;
        rat_zero(&s->lower[j]); rat_zero(&s->upper[j]);
        rat_zero(&s->value[j]);
    }
    for (i = 0; i < rows; i++) {
        b = inputs + i;
        s->basic[i] = b; s->is_basic[b] = 1;
        s->has_upper[b] = 1;
        s->rhs[i].num = c[i][0]; s->rhs[i].den = 1;
        for (j = 0; j < s->vars; j++) {
            rat_zero(&s->a[i][j]);
            if (j < inputs) s->a[i][j].num = c[i][j + 1];
        }
    }
    return sx_recompute(s);
}

/* direction=1 means increase the basic variable; -1 means decrease it.
 * Pick the smallest variable index, independent of physical row ordering.
 */
int sx_find_violation(struct SxState *s, int *row, int *direction) {
    int i, b, cmp, d, best = s->vars;
    *row = -1; *direction = 0;
    for (i = 0; i < s->rows; i++) {
        b = s->basic[i]; d = 0;
        if (s->has_lower[b]) {
            if (!rat_compare(&s->value[b], &s->lower[b], &cmp)) return 0;
            if (cmp < 0) d = 1;
        }
        if (s->has_upper[b]) {
            if (!rat_compare(&s->value[b], &s->upper[b], &cmp)) return 0;
            if (cmp > 0) d = -1;
        }
        if (d != 0 && b < best) {
            best = b; *row = i; *direction = d;
        }
    }
    return 1;
}

int sx_find_entering(struct SxState *s, int row, int direction, int *entering) {
    int j, increase, cmp;
    *entering = -1;
    for (j = 0; j < s->vars; j++) {
        if (!s->is_basic[j] && s->a[row][j].num != 0) {
            increase = (s->a[row][j].num > 0 && direction > 0) ||
                       (s->a[row][j].num < 0 && direction < 0);
            if (increase) {
                if (!s->has_upper[j]) { *entering = j; return 1; }
                if (!rat_compare(&s->value[j], &s->upper[j], &cmp)) return 0;
                if (cmp < 0) { *entering = j; return 1; }
            } else {
                if (!s->has_lower[j]) { *entering = j; return 1; }
                if (!rat_compare(&s->value[j], &s->lower[j], &cmp)) return 0;
                if (cmp > 0) { *entering = j; return 1; }
            }
        }
    }
    return 1;
}

int sx_pivot(struct SxState *s, int row, int entering) {
    int i, j, leaving = s->basic[row];
    struct SxRat pivot, factor, term, one;
    pivot = s->a[row][entering];
    one.num = 1; one.den = 1;
    if (!rat_div(&s->rhs[row], &pivot, &s->rhs[row])) return 0;
    s->rhs[row].num = -s->rhs[row].num;
    for (j = 0; j < s->vars; j++) {
        if (j != entering) {
            if (!rat_div(&s->a[row][j], &pivot, &s->a[row][j])) return 0;
            s->a[row][j].num = -s->a[row][j].num;
        }
    }
    if (!rat_div(&one, &pivot, &s->a[row][leaving])) return 0;
    rat_zero(&s->a[row][entering]);
    for (i = 0; i < s->rows; i++) {
        if (i != row) {
            factor = s->a[i][entering];
            if (factor.num != 0) {
                if (!rat_mul(&factor, &s->rhs[row], &term)) return 0;
                if (!rat_add(&s->rhs[i], &term, &s->rhs[i])) return 0;
                for (j = 0; j < s->vars; j++) {
                    if (j != entering) {
                        if (!rat_mul(&factor, &s->a[row][j], &term)) return 0;
                        if (!rat_add(&s->a[i][j], &term, &s->a[i][j])) return 0;
                    }
                }
            }
            rat_zero(&s->a[i][entering]);
        }
    }
    s->basic[row] = entering;
    s->is_basic[leaving] = 0; s->is_basic[entering] = 1;
    return 1;
}

/* Requires a successfully initialized state, or a completed successful pivot
 * followed by bound repair and recomputation. Arbitrary state edits unsupported.
 */
int sx_solve(struct SxState *s, int pivot_limit) {
    int count = 0, row, direction, entering, leaving;
    if (pivot_limit < 0) return SX_UNKNOWN;
    for (;;) {
        if (!sx_find_violation(s, &row, &direction)) return SX_UNKNOWN;
        if (row < 0) return SX_FEASIBLE;
        if (!sx_find_entering(s, row, direction, &entering)) return SX_UNKNOWN;
        if (entering < 0) return SX_UNSAT;
        if (count >= pivot_limit) return SX_UNKNOWN;
        leaving = s->basic[row];
        if (!sx_pivot(s, row, entering)) return SX_UNKNOWN;
        if (direction > 0) s->value[leaving] = s->lower[leaving];
        else s->value[leaving] = s->upper[leaving];
        if (!sx_recompute(s)) return SX_UNKNOWN;
        count++;
    }
}

int sx_check(struct SxState *s, int rows, int inputs,
             const int c[SX_ROWS][SX_INPUT_VARS + 1], int pivot_limit) {
    if (!sx_initialize(s, rows, inputs, c)) return SX_UNKNOWN;
    return sx_solve(s, pivot_limit);
}

int simplex_deduction(struct SxState *s, const struct InequList *list,
                       int inputs, int pivot_limit,
                       int c[SX_ROWS][SX_INPUT_VARS + 1]) {
    int rows = 0, j;
    const struct InequList *p = list;
    if (inputs < 0 || inputs > SX_INPUT_VARS) return SX_UNKNOWN;
    while (p != 0) {
        if (rows >= SX_ROWS || p->coef == 0) return SX_UNKNOWN;
        for (j = 0; j <= inputs; j++) c[rows][j] = p->coef[j];
        rows++;
        p = p->next;
    }
    return sx_check(s, rows, inputs, c, pivot_limit);
}

/* Original local-workspace implementation retained for comparison. */
int simplex_deduction_legacy(struct SxState *s, const struct InequList *list,
                       int inputs, int pivot_limit) {
    int c[SX_ROWS][SX_INPUT_VARS + 1];
    int rows = 0, j;
    const struct InequList *p = list;
    if (inputs < 0 || inputs > SX_INPUT_VARS) return SX_UNKNOWN;
    while (p != 0) {
        if (rows >= SX_ROWS || p->coef == 0) return SX_UNKNOWN;
        for (j = 0; j <= inputs; j++) c[rows][j] = p->coef[j];
        rows++;
        p = p->next;
    }
    return sx_check(s, rows, inputs, c, pivot_limit);
}
