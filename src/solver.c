#include "backend.h"
#include <stdint.h>
#include <stdlib.h>

struct table {
    size_t rows, cols;
    mpz_ptr d, c, a;
    size_t *basic, *row;
};

static mpz_ptr integers(size_t n)
{
    mpz_ptr p = malloc(n * sizeof(*p));
    for (size_t i = 0; i < n; ++i) mpz_init(p + i);
    return p;
}

static void release(mpz_ptr p, size_t n)
{
    for (size_t i = 0; i < n; ++i) mpz_clear(p + i);
    free(p);
}

/* Positive D makes the row gcd positive; every division is exact. */
static void normalize(struct table *t, size_t r)
{
    mpz_t g, tmp;
    mpz_init(g);
    mpz_init(tmp);
    mpz_set(g, t->d + r);
    for (size_t j = 0; j <= t->cols; ++j) {
        if (g->_mp_size == 1 && g->_mp_d[0] == 1) break;
        mpz_srcptr x = j == t->cols ? t->c + r : t->a + r * t->cols + j;
        if (x->_mp_size == 0) continue;
        mpz_gcd(tmp, g, x);
        mpz_set(g, tmp);
    }
    if (!(g->_mp_size == 1 && g->_mp_d[0] == 1)) {
        mpz_divexact(tmp, t->d + r, g);
        mpz_set(t->d + r, tmp);
        for (size_t j = 0; j <= t->cols; ++j) {
            mpz_ptr x = j == t->cols ? t->c + r : t->a + r * t->cols + j;
            if (x->_mp_size == 0) continue;
            mpz_divexact(tmp, x, g);
            mpz_set(x, tmp);
        }
    }
    mpz_clear(g);
    mpz_clear(tmp);
}

/* All arithmetic outputs use scratch distinct from their input operands. */
static void pivot(struct table *t, size_t r, size_t e)
{
    size_t b = t->basic[r], k = t->cols;
    mpz_ptr a = t->a + r * k;
    int positive = a[e]._mp_size > 0;
    mpz_t p, g, m, n, tmp;
    mpz_init(p);
    mpz_init(g);
    mpz_init(m);
    mpz_init(n);
    mpz_init(tmp);
    mpz_abs(p, a + e);
    /* P*x_e = -sign(h)*C + sign(h)*D*x_b
       - sign(h)*sum_{v != e} A_v*x_v. */
    if (positive) {
        mpz_neg(tmp, t->c + r);
        mpz_set(t->c + r, tmp);
        for (size_t v = 0; v < k; ++v) {
            mpz_neg(tmp, a + v);
            mpz_set(a + v, tmp);
        }
        mpz_set(a + b, t->d + r);
    } else {
        mpz_neg(tmp, t->d + r);
        mpz_set(a + b, tmp);
    }
    mpz_set_ui(a + e, 0);
    mpz_set(t->d + r, p);
    normalize(t, r);
    mpz_set(p, t->d + r);
    for (size_t i = 0; i < t->rows; ++i) {
        if (i == r) continue;
        mpz_ptr ai = t->a + i * k;
        if (ai[e]._mp_size == 0) continue;
        mpz_gcd(g, p, ai + e);
        mpz_divexact(m, p, g);
        mpz_divexact(n, ai + e, g);
        mpz_mul(tmp, m, t->d + i);
        mpz_set(t->d + i, tmp);
        mpz_mul(tmp, m, t->c + i);
        mpz_addmul(tmp, n, t->c + r);
        mpz_set(t->c + i, tmp);
        for (size_t v = 0; v < k; ++v) {
            if (v == e) continue;
            mpz_mul(tmp, m, ai + v);
            mpz_addmul(tmp, n, a + v);
            mpz_set(ai + v, tmp);
        }
        mpz_set_ui(ai + e, 0);
        normalize(t, i);
    }
    t->basic[r] = e;
    t->row[e] = r;
    t->row[b] = SIZE_MAX;
    mpz_clear(p);
    mpz_clear(g);
    mpz_clear(m);
    mpz_clear(n);
    mpz_clear(tmp);
}

static struct table build(const struct InequList *head, size_t variables)
{
    struct table t;
    t.rows = 0;
    for (const struct InequList *q = head; q; q = q->next)
        ++t.rows;
    t.cols = variables + t.rows;
    t.d = integers(t.rows);
    t.c = integers(t.rows);
    t.a = integers(t.rows * t.cols);
    t.basic = malloc(t.rows * sizeof(*t.basic));
    t.row = malloc(t.cols * sizeof(*t.row));
    for (size_t v = 0; v < t.cols; ++v)
        t.row[v] = SIZE_MAX;
    const struct InequList *q = head;
    for (size_t r = 0; r < t.rows; ++r, q = q->next) {
        mpz_set_ui(t.d + r, 1);
        mpz_set(t.c + r, q->coef);
        for (size_t v = 0; v < variables; ++v)
            mpz_set(t.a + r * t.cols + v, q->coef + v + 1);
        t.basic[r] = variables + r;
        t.row[variables + r] = r;
    }
    return t;
}

static void destroy(struct table *t)
{
    release(t->d, t->rows);
    release(t->c, t->rows);
    release(t->a, t->rows * t->cols);
    free(t->basic);
    free(t->row);
}

static size_t violated(const struct table *t, size_t variables)
{
    for (size_t v = variables; v < t->cols; ++v)
        if (t->row[v] != SIZE_MAX && t->c[t->row[v]]._mp_size > 0)
            return t->row[v];
    return SIZE_MAX;
}

static size_t entering(const struct table *t, size_t variables, size_t r)
{
    for (size_t v = 0; v < t->cols; ++v) {
        int sign = t->a[r * t->cols + v]._mp_size;
        if (t->row[v] == SIZE_MAX && (v < variables ? sign != 0 : sign > 0))
            return v;
    }
    return SIZE_MAX;
}

int sx_check_qcp(const struct InequList *head, size_t variables)
{
    /* A positive constant-only input row is already a contradiction. */
    for (const struct InequList *q = head; q; q = q->next) {
        if (q->coef[0]._mp_size <= 0) continue;
        size_t j = 0;
        while (j < variables && q->coef[j + 1]._mp_size == 0) ++j;
        if (j == variables) return 1;
    }
    struct table t = build(head, variables);
    int result;
    for (;;) {
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
        pivot(&t, r, e);
    }
    destroy(&t);
    return result;
}
