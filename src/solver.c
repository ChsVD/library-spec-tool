#include "backend.h"
#include <stdint.h>
#include <stdlib.h>




void mpz_tdiv_r(mpz_ptr, mpz_srcptr, mpz_srcptr);

struct table {
    size_t rows, cols;
    mpz_ptr d, c, a;
    size_t *basic, *row;
    size_t *nonbasic;
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
    mpz_t remainder;
    mpz_init(remainder);
    mpz_set(g, t->d + r);
    for (size_t slot = 0; slot <= t->cols - t->rows; ++slot) {
        size_t j = slot == t->cols - t->rows ? t->cols : t->nonbasic[slot];
        if (g->_mp_size == 1 && g->_mp_d[0] == 1) break;
        if (j < t->cols && t->row[j] != SIZE_MAX) continue;
        mpz_srcptr x = j == t->cols ? t->c + r : t->a + r * t->cols + j;
        if (x->_mp_size == 0) continue;
        /* g>0; gcd(g,x)=gcd(g,x mod g), including negative x. */
        mpz_tdiv_r(remainder, x, g);
        if (remainder->_mp_size == 0) continue;
        mpz_gcd(tmp, g, remainder);
        mpz_set(g, tmp);
    }
    if (!(g->_mp_size == 1 && g->_mp_d[0] == 1)) {
        mpz_divexact(tmp, t->d + r, g);
        mpz_set(t->d + r, tmp);
        for (size_t slot = 0; slot <= t->cols - t->rows; ++slot) {
            size_t j = slot == t->cols - t->rows ? t->cols : t->nonbasic[slot];
            if (j < t->cols && t->row[j] != SIZE_MAX) continue;
            mpz_ptr x = j == t->cols ? t->c + r : t->a + r * t->cols + j;
            if (x->_mp_size == 0) continue;
            mpz_divexact(tmp, x, g);
            mpz_set(x, tmp);
        }
    }
    mpz_clear(remainder);
    mpz_clear(g);
    mpz_clear(tmp);
}

/* Output is scratch, distinct from all operands. M is positive. */
static void combine(mpz_ptr out, mpz_srcptr m, mpz_srcptr a,
                    mpz_srcptr n, mpz_srcptr b)
{
    if (a->_mp_size == 0) {
        if (b->_mp_size == 0)
            mpz_set_ui(out, 0);
        else
            mpz_mul(out, n, b);
        return;
    }
    if (m->_mp_size == 1 && m->_mp_d[0] == 1)
        mpz_set(out, a);
    else
        mpz_mul(out, m, a);
    if (b->_mp_size != 0)
        mpz_addmul(out, n, b);
}

/* All arithmetic outputs use scratch distinct from their input operands. */
static void pivot(struct table *t, size_t r, size_t e)
{
    size_t b = t->basic[r], k = t->cols;
    mpz_ptr a = t->a + r * k;
    int positive = a[e]._mp_size > 0;
    __mpz_struct p, g, m, n, tmp;
    mpz_init(&p);
    mpz_init(&g);
    mpz_init(&m);
    mpz_init(&n);
    mpz_init(&tmp);
    mpz_abs(&p, a + e);
    /* P*x_e = -sign(h)*C + sign(h)*D*x_b
       - sign(h)*sum_{v != e} A_v*x_v. */
    if (positive) {
        mpz_neg(&tmp, t->c + r);
        mpz_set(t->c + r, &tmp);
        for (size_t slot = 0; slot < t->cols - t->rows; ++slot) {
            size_t v = t->nonbasic[slot];
            if (t->row[v] != SIZE_MAX) continue;
            mpz_neg(&tmp, a + v);
            mpz_set(a + v, &tmp);
        }
        mpz_set(a + b, t->d + r);
    } else {
        mpz_neg(&tmp, t->d + r);
        mpz_set(a + b, &tmp);
    }
    mpz_set_ui(a + e, 0);
    mpz_set(t->d + r, &p);
    /* Replace exactly the entering slot; list order never controls selection. */
    for (size_t slot = 0; slot < t->cols - t->rows; ++slot)
        if (t->nonbasic[slot] == e) {
            t->nonbasic[slot] = b;
            break;
        }
    /* The leaving column is now nonbasic and must participate below. */
    t->basic[r] = e;
    t->row[e] = r;
    t->row[b] = SIZE_MAX;
    normalize(t, r);
    mpz_set(&p, t->d + r);
    for (size_t i = 0; i < t->rows; ++i) {
        if (i == r) continue;
        mpz_ptr ai = t->a + i * k;
        if (ai[e]._mp_size == 0) continue;
        mpz_gcd(&g, &p, ai + e);
        mpz_divexact(&m, &p, &g);
        mpz_divexact(&n, ai + e, &g);
        if (m._mp_size == 1 && m._mp_d[0] == 1)
            mpz_set(&tmp, t->d + i);
        else
        mpz_mul(&tmp, &m, t->d + i);
        mpz_set(t->d + i, &tmp);
        combine(&tmp, &m, t->c + i, &n, t->c + r);
        mpz_set(t->c + i, &tmp);
        for (size_t slot = 0; slot < t->cols - t->rows; ++slot) {
            size_t v = t->nonbasic[slot];
            if (v == e) continue;
            if (t->row[v] != SIZE_MAX) continue;
            combine(&tmp, &m, ai + v, &n, a + v);
            mpz_set(ai + v, &tmp);
        }
        mpz_set_ui(ai + e, 0);
        normalize(t, i);
    }
    mpz_clear(&p);
    mpz_clear(&g);
    mpz_clear(&m);
    mpz_clear(&n);
    mpz_clear(&tmp);
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
    t.nonbasic = malloc(variables * sizeof(*t.nonbasic));
    for (size_t v = 0; v < variables; ++v)
        t.nonbasic[v] = v;
    for (size_t v = 0; v < t.cols; ++v)
        t.row[v] = SIZE_MAX;
    const struct InequList *q = head;
    for (size_t r = 0; r < t.rows;) {
        mpz_set_ui(t.d + r, 1);
        mpz_set(t.c + r, q->coef);
        for (size_t v = 0; v < variables; ++v)
            mpz_set(t.a + r * t.cols + v, q->coef + v + 1);
        t.basic[r] = variables + r;
        t.row[variables + r] = r;
        ++r;
        q = q->next;
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
    free(t->nonbasic);
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

/* One original-system sign scan. Each removed row contains a selected
   variable; moving all selected variables in their decreasing directions
   satisfies these rows without changing any retained row. */
static struct table build_one_sided(const struct InequList *head, size_t variables)
{
    unsigned char *signs = calloc(variables, sizeof(*signs));
    size_t rows = 0;
    for (const struct InequList *q = head; q; q = q->next) {
        ++rows;
        for (size_t j = 0; j < variables; ++j) {
            int sign = q->coef[j + 1]._mp_size;
            if (sign > 0) signs[j] |= 1;
            if (sign < 0) signs[j] |= 2;
        }
    }
    struct InequList *nodes = malloc(rows * sizeof(*nodes));
    size_t kept = 0;
    for (const struct InequList *q = head; q; q = q->next) {
        size_t j = 0;
        while (j < variables) {
            if ((signs[j] == 1 || signs[j] == 2) &&
                q->coef[j + 1]._mp_size != 0) break;
            ++j;
        }
        if (j != variables) continue;
        nodes[kept].coef = q->coef;
        nodes[kept].next = NULL;
        if (kept != 0) nodes[kept - 1].next = nodes + kept;
        ++kept;
    }
    struct table t = build(kept ? nodes : NULL, variables);
    free(nodes);
    free(signs);
    return t;
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
    struct table t = build_one_sided(head, variables);
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


