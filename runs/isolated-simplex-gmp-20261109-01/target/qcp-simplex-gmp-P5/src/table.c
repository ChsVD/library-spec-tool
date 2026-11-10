#include "runtime_scope.h"
#include "sx_table.h"
#include <limits.h>
#include <stdint.h>
#include <string.h>

/* Matches original fme_gmp.c, not an extended node format. */
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};
struct SxTable {
    size_t m, n, total, rat_count, original_count, coefficient_count;
    SxRat *rats, *original, *beta, *coeff, *value, *lower, *upper;
    size_t *indices, *basic, *nonbasic, *row, *column;
    unsigned char *flags;
};
typedef struct {
    SxScope scope;
    SxLimits arith;
    SxError error;
    SxTableReason reason;
    SxArithReason ar;
} Work;
static SxError fail(Work *w, SxError e, SxTableReason r) {
    w->error = e;
    w->reason = r;
    return e;
}
static int sizeadd(Work *w, size_t a, size_t b, size_t *out) {
    if (b > SIZE_MAX - a) {
        fail(w, SX_LIMIT, SX_T_OVERFLOW);
        return 0;
    }
    *out = a + b;
    return 1;
}
static int sizemul(Work *w, size_t a, size_t b, size_t *out) {
    if (a && b > SIZE_MAX / a) {
        fail(w, SX_LIMIT, SX_T_OVERFLOW);
        return 0;
    }
    *out = a * b;
    return 1;
}
static void *alloc(Work *w, size_t n) {
    void *p = sx_scope_alloc(n);
    if (!p) {
        w->ar = w->scope.reason;
        fail(w, w->scope.error,
             w->ar == SX_AR_BYTES           ? SX_T_TOTAL_BYTES
             : w->ar == SX_AR_SIZE_OVERFLOW ? SX_T_OVERFLOW
                                            : SX_T_ALLOC);
    }
    return p;
}
static SxError arithmetic(Work *w, SxError e, const SxStats *s) {
    if (e) {
        w->ar = s->reason;
        SxTableReason r = SX_T_OBJECT;
        switch (s->reason) {
        case SX_AR_BYTES:
            r = w->scope.reason == SX_AR_BYTES ? SX_T_TOTAL_BYTES : SX_T_ARITH_BYTES;
            break;
        case SX_AR_LIMBS:
            r = SX_T_LIMBS;
            break;
        case SX_AR_SIZE_OVERFLOW:
            r = SX_T_OVERFLOW;
            break;
        case SX_AR_ALLOC:
            r = SX_T_ALLOC;
            break;
        case SX_AR_REENTRY:
            r = SX_T_REENTRY;
            break;
        default:
            break;
        }
        fail(w, e, r);
    }
    return e;
}
static int op(Work *w, SxRat *out, char c, const SxRat *a, const SxRat *b) {
    SxStats s;
    SxError e = sx_rat_op(out, c, a, b, &w->arith, &s);
    return arithmetic(w, e, &s) == SX_OK;
}
static int copy(Work *w, SxRat *out, const SxRat *a) {
    SxRat z;
    sx_rat_init(&z);
    return op(w, out, '+', a, &z);
}
static int import(Work *w, SxRat *out, mpz_srcptr z) {
    SxStats s;
    SxError e = sx_rat_import(out, z, &w->arith, &s);
    return arithmetic(w, e, &s) == SX_OK;
}
static int compare(Work *w, const SxRat *a, const SxRat *b, int *out) {
    SxStats s;
    SxError e = sx_rat_cmp(out, a, b, &w->arith, &s);
    return arithmetic(w, e, &s) == SX_OK;
}
static SxRat *at(SxTable *t, size_t i, size_t v) {
    return &t->coeff[i * t->total + v];
}
static const SxRat *cat(const SxTable *t, size_t i, size_t v) {
    return &t->coeff[i * t->total + v];
}
void sx_table_destroy(SxTable *t) {
    if (!t)
        return;
    if (t->rats) {
        for (size_t i = 0; i < t->rat_count; i++)
            sx_rat_clear(&t->rats[i]);
    }
    sx_scope_free(t->rats);
    sx_scope_free(t->indices);
    sx_scope_free(t->flags);
    sx_scope_free(t);
}
size_t sx_table_bytes(const SxTable *t) {
    if (!t)
        return 0;
    size_t n = sx_scope_size(t) + sx_scope_size(t->rats) + sx_scope_size(t->indices) +
               sx_scope_size(t->flags);
    for (size_t i = 0; i < t->rat_count; i++)
        n += sx_rat_bytes(&t->rats[i]);
    return n;
}
static SxTable *empty(Work *w, size_t m, size_t n) {
    size_t total, width, oc, cc, rc, extra, ic, bytes, flagbytes;
    if (!sizeadd(w, m, n, &total) || !sizeadd(w, n, 1, &width) || !sizemul(w, m, width, &oc) ||
        !sizemul(w, m, total, &cc) || !sizemul(w, total, 3, &extra) || !sizeadd(w, oc, cc, &rc) ||
        !sizeadd(w, rc, m, &rc) || !sizeadd(w, rc, extra, &rc) || !sizemul(w, total, 3, &ic) ||
        !sizemul(w, total, 2, &flagbytes))
        return NULL;
    SxTable *t = alloc(w, sizeof(*t));
    if (!t)
        return NULL;
    t->m = m;
    t->n = n;
    t->total = total;
    t->original_count = oc;
    t->coefficient_count = cc;
    if (!sizemul(w, rc, sizeof(SxRat), &bytes))
        goto bad;
    t->rats = alloc(w, bytes);
    if (!t->rats)
        goto bad;
    for (size_t i = 0; i < rc; i++) {
        sx_rat_init(&t->rats[i]);
        t->rat_count++;
    }
    t->original = t->rats;
    t->beta = t->original + oc;
    t->coeff = t->beta + m;
    t->value = t->coeff + cc;
    t->lower = t->value + total;
    t->upper = t->lower + total;
    if (!sizemul(w, ic, sizeof(size_t), &bytes))
        goto bad;
    t->indices = alloc(w, bytes);
    if (!t->indices)
        goto bad;
    t->basic = t->indices;
    t->nonbasic = t->basic + m;
    t->row = t->nonbasic + n;
    t->column = t->row + total;
    for (size_t v = 0; v < total; v++)
        t->row[v] = t->column[v] = SIZE_MAX;
    t->flags = alloc(w, flagbytes);
    if (!t->flags)
        goto bad;
    return t;
bad:
    sx_table_destroy(t);
    return NULL;
}
static SxTable *clone(Work *w, const SxTable *old) {
    SxTable *t = empty(w, old->m, old->n);
    if (!t)
        return NULL;
    for (size_t i = 0; i < t->rat_count; i++)
        if (!copy(w, &t->rats[i], &old->rats[i])) {
            sx_table_destroy(t);
            return NULL;
        }
    if (t->total) {
        memcpy(t->indices, old->indices, 3 * t->total * sizeof(size_t));
        memcpy(t->flags, old->flags, 2 * t->total);
    }
    return t;
}
static int allowed(Work *w, const SxTable *t, size_t v, const SxRat *x) {
    int c;
    if (t->flags[2 * v]) {
        if (!compare(w, x, &t->lower[v], &c))
            return 0;
        if (c < 0) {
            fail(w, SX_INVALID, SX_T_BOUND);
            return 0;
        }
    }
    if (t->flags[2 * v + 1]) {
        if (!compare(w, x, &t->upper[v], &c))
            return 0;
        if (c > 0) {
            fail(w, SX_INVALID, SX_T_BOUND);
            return 0;
        }
    }
    return 1;
}
static int sumrow(Work *w, const SxTable *t, size_t i, SxRat *out) {
    SxRat p;
    sx_rat_init(&p);
    int ok = copy(w, out, &t->beta[i]);
    for (size_t j = 0; ok && j < t->n; j++) {
        size_t v = t->nonbasic[j];
        if (!cat(t, i, v)->num._mp_size)
            continue;
        ok = op(w, &p, '*', cat(t, i, v), &t->value[v]) && op(w, out, '+', out, &p);
    }
    sx_rat_clear(&p);
    return ok;
}
static int recompute(Work *w, SxTable *t) {
    for (size_t i = 0; i < t->m; i++)
        if (!sumrow(w, t, i, &t->value[t->basic[i]]))
            return 0;
    return 1;
}
static int move(Work *w, SxTable *t, size_t v, const SxRat *x) {
    if (!allowed(w, t, v, x))
        return 0;
    SxRat delta, p;
    sx_rat_init(&delta);
    sx_rat_init(&p);
    int ok = op(w, &delta, '-', x, &t->value[v]);
    for (size_t i = 0; ok && i < t->m; i++) {
        if (!at(t, i, v)->num._mp_size)
            continue;
        ok = op(w, &p, '*', at(t, i, v), &delta) &&
             op(w, &t->value[t->basic[i]], '+', &t->value[t->basic[i]], &p);
    }
    if (ok)
        ok = copy(w, &t->value[v], x);
    sx_rat_clear(&delta);
    sx_rat_clear(&p);
    return ok;
}
static int pivot(Work *w, SxTable *t, size_t r, size_t e, int lower) {
    size_t b = t->basic[r];
    SxRat target, delta, p, a, d, tmp, unit, neg;
    sx_rat_init(&target);
    sx_rat_init(&delta);
    sx_rat_init(&p);
    sx_rat_init(&a);
    sx_rat_init(&d);
    sx_rat_init(&tmp);
    sx_rat_init(&unit);
    sx_rat_init(&neg);
    int ok = 0, c;
    if (!t->flags[2 * b + (lower ? 0 : 1)] || !at(t, r, e)->num._mp_size) {
        fail(w, SX_INVALID, SX_T_PIVOT);
        goto done;
    }
    if (!copy(w, &target, lower ? &t->lower[b] : &t->upper[b]) ||
        !compare(w, &t->value[b], &target, &c))
        goto done;
    if ((lower && c >= 0) || (!lower && c <= 0)) {
        fail(w, SX_INVALID, SX_T_PIVOT);
        goto done;
    }
    if (!copy(w, &a, at(t, r, e)) || !op(w, &delta, '-', &target, &t->value[b]) ||
        !op(w, &delta, '/', &delta, &a))
        goto done;
    /* Only direction availability is required, not the full delta within bounds. */
    if (delta.num._mp_size > 0 && t->flags[2 * e + 1]) {
        if (!compare(w, &t->value[e], &t->upper[e], &c))
            goto done;
        if (c >= 0) {
            fail(w, SX_INVALID, SX_T_PIVOT);
            goto done;
        }
    }
    if (delta.num._mp_size < 0 && t->flags[2 * e]) {
        if (!compare(w, &t->value[e], &t->lower[e], &c))
            goto done;
        if (c <= 0) {
            fail(w, SX_INVALID, SX_T_PIVOT);
            goto done;
        }
    }
    /* Increment old assignment from the old pivot column before changing rows. */
    for (size_t i = 0; i < t->m; i++) {
        if (!at(t, i, e)->num._mp_size)
            continue;
        if (!op(w, &p, '*', at(t, i, e), &delta) ||
            !op(w, &t->value[t->basic[i]], '+', &t->value[t->basic[i]], &p))
            goto done;
    }
    if (!op(w, &t->value[e], '+', &t->value[e], &delta) || !copy(w, &t->value[b], &target))
        goto done;
    {
        unsigned int limb = 1;
        __mpz_struct z = {0, 1, &limb};
        if (!import(w, &unit, &z))
            goto done;
    }
    if (!op(w, &neg, '-', &neg, &unit) || !op(w, &t->beta[r], '/', &t->beta[r], &a) ||
        !op(w, &t->beta[r], '*', &t->beta[r], &neg))
        goto done;
    for (size_t j = 0; j < t->n; j++) {
        size_t v = t->nonbasic[j];
        if (v == e)
            continue;
        if (!at(t, r, v)->num._mp_size)
            continue;
        if (!op(w, at(t, r, v), '/', at(t, r, v), &a) ||
            !op(w, at(t, r, v), '*', at(t, r, v), &neg))
            goto done;
    }
    if (!op(w, at(t, r, b), '/', &unit, &a))
        goto done;
    sx_rat_clear(at(t, r, e));
    for (size_t i = 0; i < t->m; i++) {
        if (i == r || !at(t, i, e)->num._mp_size)
            continue;
        if (!copy(w, &d, at(t, i, e)) || !op(w, &tmp, '*', &d, &t->beta[r]) ||
            !op(w, &t->beta[i], '+', &t->beta[i], &tmp))
            goto done;
        for (size_t j = 0; j < t->n; j++) {
            size_t v = t->nonbasic[j];
            if (v == e)
                continue;
            if (!at(t, r, v)->num._mp_size)
                continue;
            if (!op(w, &tmp, '*', &d, at(t, r, v)) || !op(w, at(t, i, v), '+', at(t, i, v), &tmp))
                goto done;
        }
        if (!op(w, at(t, i, b), '*', &d, at(t, r, b)))
            goto done;
        sx_rat_clear(at(t, i, e));
    }
    {
        size_t col = t->column[e];
        t->nonbasic[col] = b;
        t->basic[r] = e;
        t->column[e] = SIZE_MAX;
        t->row[b] = SIZE_MAX;
        t->row[e] = r;
        t->column[b] = col;
    }
    ok = 1;
done:
    sx_rat_clear(&target);
    sx_rat_clear(&delta);
    sx_rat_clear(&p);
    sx_rat_clear(&a);
    sx_rat_clear(&d);
    sx_rat_clear(&tmp);
    sx_rat_clear(&unit);
    sx_rat_clear(&neg);
    return ok;
}
static int raw_equal(mpz_srcptr a, mpz_srcptr b) {
    if (a->_mp_size != b->_mp_size)
        return 0;
    size_t n = (size_t)(a->_mp_size < 0 ? -a->_mp_size : a->_mp_size);
    return !n || !memcmp(a->_mp_d, b->_mp_d, n * sizeof(unsigned int));
}
static int external(Work *w, const SxRat *q) {
    SxRat n, d, z;
    sx_rat_init(&n);
    sx_rat_init(&d);
    sx_rat_init(&z);
    int ok = 0;
    if (!q || q->den._mp_size <= 0) {
        fail(w, SX_INVALID, SX_T_OBJECT);
        goto done;
    }
    if (!import(w, &n, &q->num) || !import(w, &d, &q->den) || !op(w, &z, '/', &n, &d))
        goto done;
    if (!raw_equal(&z.num, &q->num) || !raw_equal(&z.den, &q->den)) {
        fail(w, SX_INVALID, SX_T_OBJECT);
        goto done;
    }
    ok = 1;
done:
    sx_rat_clear(&n);
    sx_rat_clear(&d);
    sx_rat_clear(&z);
    return ok;
}
static int invariant(Work *w, const SxTable *t) {
    SxRat x, y, z, p;
    sx_rat_init(&x);
    sx_rat_init(&y);
    sx_rat_init(&z);
    sx_rat_init(&p);
    int ok = 0, c;
    for (size_t v = 0; v < t->total; v++) {
        size_t r = t->row[v], j = t->column[v];
        if ((r == SIZE_MAX) == (j == SIZE_MAX) ||
            (r != SIZE_MAX && (r >= t->m || t->basic[r] != v)) ||
            (j != SIZE_MAX && (j >= t->n || t->nonbasic[j] != v)))
            goto mismatch;
        if (j != SIZE_MAX && !allowed(w, t, v, &t->value[v])) {
            if (w->error == SX_INVALID)
                fail(w, SX_INTERNAL, SX_T_INVARIANT);
            goto done;
        }
    }
    for (size_t k = 0; k < t->rat_count; k++) {
        const SxRat *q = &t->rats[k];
        if (q->den._mp_size <= 0)
            goto mismatch;
        if (!import(w, &x, &q->num) || !import(w, &y, &q->den) || !op(w, &z, '/', &x, &y))
            goto done;
        if (!raw_equal(&z.num, &q->num) || !raw_equal(&z.den, &q->den))
            goto mismatch;
    }
    for (size_t i = 0; i < t->m; i++) {
        for (size_t j = 0; j < t->m; j++)
            if (cat(t, i, t->basic[j])->num._mp_size)
                goto mismatch;
        if (!sumrow(w, t, i, &x) || !compare(w, &x, &t->value[t->basic[i]], &c))
            goto done;
        if (c)
            goto mismatch;
    }
    /* Symbolically substitute the current solved rows into every ORIGINAL equation.
       All constant and nonbasic coefficients must vanish; this checks equivalence,
       independently of the current valuation. Original system has row rank m. */
    for (size_t i = 0; i < t->m; i++)
        for (size_t j = 0; j <= t->n; j++) {
            sx_rat_clear(&x);
            if (j == 0 && !op(w, &x, '-', &x, &t->original[i * (t->n + 1)]))
                goto done;
            for (size_t v = 0; v < t->total; v++) {
                sx_rat_clear(&y);
                if (v < t->n) {
                    if (!op(w, &y, '-', &y, &t->original[i * (t->n + 1) + v + 1]))
                        goto done;
                } else if (v == t->n + i) {
                    unsigned int limb = 1;
                    __mpz_struct zi = {0, 1, &limb};
                    if (!import(w, &y, &zi))
                        goto done;
                } else
                    continue;
                if (!y.num._mp_size)
                    continue;
                size_t br = t->row[v];
                if (br != SIZE_MAX) {
                    const SxRat *f = j == 0 ? &t->beta[br] : cat(t, br, t->nonbasic[j - 1]);
                    if (!op(w, &p, '*', &y, f) || !op(w, &x, '+', &x, &p))
                        goto done;
                } else if (j && t->nonbasic[j - 1] == v) {
                    if (!op(w, &x, '+', &x, &y))
                        goto done;
                }
            }
            if (x.num._mp_size)
                goto mismatch;
        }
    ok = 1;
    goto done;
mismatch:
    fail(w, SX_INTERNAL, SX_T_INVARIANT);
done:
    sx_rat_clear(&x);
    sx_rat_clear(&y);
    sx_rat_clear(&z);
    sx_rat_clear(&p);
    return ok;
}
static SxError start(Work *w, const SxTable *t, const SxTableLimits *l, SxTableStats *s) {
    memset(w, 0, sizeof(*w));
    if (s)
        memset(s, 0, sizeof(*s));
    if (l)
        w->arith = l->arithmetic;
    if ((w->arith.max_limbs &&
         (w->arith.max_limbs < 4 || w->arith.max_limbs > (size_t)INT_MAX / 64)) ||
        w->arith.fail_at) {
        w->ar = SX_AR_BAD_ARGUMENT;
        return fail(w, SX_INVALID, SX_T_ARGUMENT);
    }
    w->arith.fail_at = 0;
    size_t lim = l && l->max_table_bytes ? l->max_table_bytes : 256 * 1024 * 1024;
    SxError e = sx_scope_begin(&w->scope, sx_table_bytes(t), lim, l ? l->fail_at : 0);
    if (e) {
        w->ar = w->scope.reason;
        fail(w, e, w->ar == SX_AR_REENTRY ? SX_T_REENTRY : SX_T_TOTAL_BYTES);
    }
    return e;
}
static SxError finish(Work *w, SxTable *candidate, SxTable **out, const SxTable *old,
                      SxTableStats *s) {
    if (w->error)
        sx_table_destroy(candidate);
    size_t bytes = sx_table_bytes(w->error ? old : candidate ? candidate : old);
    sx_scope_end(&w->scope);
    if (!w->error && out) {
        sx_table_destroy(*out);
        *out = candidate;
    }
    if (s) {
        s->reason = w->reason;
        s->arithmetic_reason = w->ar;
        s->allocations = w->scope.attempts;
        s->peak_table_bytes = w->scope.peak;
        s->retained_table_bytes = bytes;
    }
    return w->error;
}
static SxError badstats(SxTableStats *s, SxTableReason r) {
    if (s) {
        memset(s, 0, sizeof(*s));
        s->reason = r;
    }
    return SX_INVALID;
}
static SxError create(SxTable **out, const SxProblem *input, const struct InequList *list,
                      size_t rows, size_t vars, int qcp, const SxTableLimits *l, SxTableStats *s) {
    if (!out || *out)
        return badstats(s, SX_T_ARGUMENT);
    Work w;
    if (start(&w, NULL, l, s))
        return finish(&w, NULL, NULL, NULL, s);
    SxTable *t = empty(&w, rows, vars);
    if (!t)
        return finish(&w, NULL, NULL, NULL, s);
    const struct InequList *node = list;
    for (size_t i = 0; i < rows; i++) {
        mpz_srcptr data = qcp ? node->coef : input->coefficients + i * (vars + 1);
        if (!data) {
            fail(&w, SX_INVALID, SX_T_OBJECT);
            break;
        }
        for (size_t j = 0; j <= vars; j++)
            if (!import(&w, &t->original[i * (vars + 1) + j], &data[j]))
                break;
        if (w.error)
            break;
        if (!copy(&w, &t->beta[i], &t->original[i * (vars + 1)]) ||
            !copy(&w, &t->value[vars + i], &t->beta[i]))
            break;
        for (size_t j = 0; j < vars; j++)
            if (!copy(&w, at(t, i, j), &t->original[i * (vars + 1) + j + 1]))
                break;
        if (w.error)
            break;
        t->basic[i] = vars + i;
        t->row[vars + i] = i;
        t->flags[2 * (vars + i) + 1] = 1;
        if (qcp)
            node = node->next;
    }
    for (size_t j = 0; j < vars; j++) {
        t->nonbasic[j] = j;
        t->column[j] = j;
    }
    if (!w.error)
        invariant(&w, t);
    return finish(&w, t, out, NULL, s);
}
SxError sx_table_create(SxTable **out, const SxProblem *p, const SxTableLimits *l,
                        SxTableStats *s) {
    if (!p || (p->rows && !p->coefficients))
        return badstats(s, SX_T_ARGUMENT);
    return create(out, p, NULL, p->rows, p->variables, 0, l, s);
}
SxError sx_table_create_qcp(SxTable **out, const struct InequList *head, size_t n,
                            const SxTableLimits *l, SxTableStats *s) {
    const struct InequList *slow = head, *fast = head;
    while (fast && fast->next) {
        slow = slow->next;
        fast = fast->next->next;
        if (slow == fast)
            return badstats(s, SX_T_CYCLE);
    }
    size_t m = 0;
    for (const struct InequList *p = head; p; p = p->next) {
        if (m == SIZE_MAX)
            return badstats(s, SX_T_DIMENSION);
        m++;
    }
    return create(out, NULL, head, m, n, 1, l, s);
}
typedef enum { MUT_BOUNDS, MUT_MOVE, MUT_PIVOT, MUT_RECOMPUTE } Mutation;
static SxError mutate(SxTable **pt, size_t v, size_t row, Mutation mode, int lower, const SxRat *a,
                      const SxRat *b, const SxTableLimits *l, SxTableStats *s) {
    if (!pt || !*pt)
        return badstats(s, SX_T_ARGUMENT);
    SxTable *old = *pt;
    if ((mode != MUT_RECOMPUTE && v >= old->total) ||
        (mode == MUT_PIVOT && (row >= old->m || old->column[v] == SIZE_MAX)) ||
        (mode == MUT_MOVE && (!a || old->column[v] == SIZE_MAX)))
        return badstats(s, SX_T_ARGUMENT);
    Work w;
    if (start(&w, old, l, s))
        return finish(&w, NULL, NULL, old, s);
    if ((mode == MUT_BOUNDS || mode == MUT_MOVE) &&
        ((a && !external(&w, a)) || (b && !external(&w, b))))
        return finish(&w, NULL, NULL, old, s);
    SxTable *t = clone(&w, old);
    if (!t)
        return finish(&w, NULL, NULL, old, s);
    if (mode == MUT_BOUNDS) {
        int c;
        if (a && b) {
            if (!compare(&w, a, b, &c))
                goto done;
            if (c > 0) {
                fail(&w, SX_INVALID, SX_T_BOUND);
                goto done;
            }
        }
        t->flags[2 * v] = (unsigned char)(a != NULL);
        t->flags[2 * v + 1] = (unsigned char)(b != NULL);
        sx_rat_clear(&t->lower[v]);
        sx_rat_clear(&t->upper[v]);
        if (a && !copy(&w, &t->lower[v], a))
            goto done;
        if (b && !copy(&w, &t->upper[v], b))
            goto done;
        if (t->column[v] != SIZE_MAX && !allowed(&w, t, v, &t->value[v]))
            goto done;
    } else if (mode == MUT_MOVE)
        move(&w, t, v, a);
    else if (mode == MUT_PIVOT)
        pivot(&w, t, row, v, lower);
    else
        recompute(&w, t);
done:
    if (!w.error)
        invariant(&w, t);
    return finish(&w, t, pt, old, s);
}
SxError sx_table_bounds(SxTable **t, size_t v, const SxRat *a, const SxRat *b,
                        const SxTableLimits *l, SxTableStats *s) {
    return mutate(t, v, 0, MUT_BOUNDS, 0, a, b, l, s);
}
SxError sx_table_move(SxTable **t, size_t v, const SxRat *a, const SxTableLimits *l,
                      SxTableStats *s) {
    return mutate(t, v, 0, MUT_MOVE, 0, a, NULL, l, s);
}
SxError sx_table_pivot(SxTable **t, size_t r, size_t e, int lower, const SxTableLimits *l,
                       SxTableStats *s) {
    if (lower != 0 && lower != 1)
        return badstats(s, SX_T_ARGUMENT);
    return mutate(t, e, r, MUT_PIVOT, lower, NULL, NULL, l, s);
}
SxError sx_table_recompute(SxTable **t, const SxTableLimits *l, SxTableStats *s) {
    return mutate(t, 0, 0, MUT_RECOMPUTE, 0, NULL, NULL, l, s);
}
SxError sx_table_check(const SxTable *t, const SxTableLimits *l, SxTableStats *s) {
    if (!t)
        return badstats(s, SX_T_ARGUMENT);
    Work w;
    if (!start(&w, t, l, s))
        invariant(&w, t);
    return finish(&w, NULL, NULL, t, s);
}
size_t sx_table_rows(const SxTable *t) {
    return t ? t->m : 0;
}
size_t sx_table_variables(const SxTable *t) {
    return t ? t->total : 0;
}
size_t sx_table_original_variables(const SxTable *t) {
    return t ? t->n : 0;
}
size_t sx_table_basic(const SxTable *t, size_t i) {
    return t && i < t->m ? t->basic[i] : SIZE_MAX;
}
size_t sx_table_nonbasic(const SxTable *t, size_t j) {
    return t && j < t->n ? t->nonbasic[j] : SIZE_MAX;
}
size_t sx_table_basic_row(const SxTable *t, size_t v) {
    return t && v < t->total ? t->row[v] : SIZE_MAX;
}
size_t sx_table_nonbasic_column(const SxTable *t, size_t v) {
    return t && v < t->total ? t->column[v] : SIZE_MAX;
}
const SxRat *sx_table_beta(const SxTable *t, size_t i) {
    return t && i < t->m ? &t->beta[i] : NULL;
}
const SxRat *sx_table_coefficient(const SxTable *t, size_t i, size_t v) {
    return t && i < t->m && v < t->total ? cat(t, i, v) : NULL;
}
const SxRat *sx_table_value(const SxTable *t, size_t v) {
    return t && v < t->total ? &t->value[v] : NULL;
}
const SxRat *sx_table_lower(const SxTable *t, size_t v) {
    return t && v < t->total && t->flags[2 * v] ? &t->lower[v] : NULL;
}
const SxRat *sx_table_upper(const SxTable *t, size_t v) {
    return t && v < t->total && t->flags[2 * v + 1] ? &t->upper[v] : NULL;
}
