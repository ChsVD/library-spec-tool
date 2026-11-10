#include "integer_ops.h"
#include "solver_types.h"
#include "table_internal.h"
#include <limits.h>
#include <stdint.h>
#include <string.h>

static _Thread_local int solving;
void sx_result_init(SxResult *r) {
    memset(r, 0, sizeof(*r));
    sx_rat_init(&r->conflict.constant);
    sx_rat_init(&r->conflict.required);
    sx_rat_init(&r->conflict.attainable);
}
void sx_result_clear(SxResult *r) {
    if (!r)
        return;
    for (size_t i = 0; i < r->witness_length; i++)
        sx_rat_clear(&r->witness[i]);
    sx_scope_free(r->witness);
    for (size_t i = 0; i < r->conflict.blocker_count; i++) {
        sx_rat_clear(&r->conflict.blockers[i].coefficient);
        sx_rat_clear(&r->conflict.blockers[i].bound);
    }
    sx_scope_free(r->conflict.blockers);
    sx_rat_clear(&r->conflict.constant);
    sx_rat_clear(&r->conflict.required);
    sx_rat_clear(&r->conflict.attainable);
    sx_result_init(r);
}
static int stop(Solve *w, SxError e, SxReason r, SxDiagnostic d) {
    w->error = e;
    w->reason = r;
    w->diagnostic = d;
    return 0;
}
static int numeric(Solve *w, SxError e, SxArithReason a) {
    if (!e)
        return 1;
    w->arithmetic_reason = a;
    if (a == SX_AR_TIME)
        return stop(w, SX_LIMIT, SX_REASON_TIME, SX_D_TIME);
    if (a == SX_AR_CLOCK)
        return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_CLOCK);
    if (a == SX_AR_REENTRY)
        return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_REENTRY);
    if (e == SX_OOM)
        return stop(w, e, SX_REASON_ALLOCATION, SX_D_ALLOC);
    if (a == SX_AR_BYTES) {
        if (w->scope.error == SX_LIMIT && w->scope.reason == SX_AR_BYTES)
            return stop(w, SX_LIMIT, SX_REASON_SPACE, SX_D_TOTAL_BYTES);
        return stop(w, SX_LIMIT, SX_REASON_ARITH_SPACE, SX_D_ARITH_BYTES);
    }
    if (a == SX_AR_LIMBS)
        return stop(w, SX_LIMIT, SX_REASON_LIMBS, SX_D_LIMBS);
    if (a == SX_AR_SIZE_OVERFLOW)
        return stop(w, SX_LIMIT, SX_REASON_SIZE_OVERFLOW, SX_D_OVERFLOW);
    return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
}
static int checkpoint(Solve *w) {
    SxError e = sx_scope_checkpoint();
    return numeric(w, e, w->scope.reason);
}
static int op(Solve *w, SxRat *q, char c, const SxRat *a, const SxRat *b) {
    SxStats s;
    SxError e = sx_rat_op(q, c, a, b, &w->limits.arithmetic, &s);
    return numeric(w, e, s.reason);
}
static int copy(Solve *w, SxRat *q, const SxRat *a) {
    SxRat z;
    sx_rat_init(&z);
    return op(w, q, '+', a, &z);
}
static int compare(Solve *w, const SxRat *a, const SxRat *b, int *c) {
    SxStats s;
    SxError e = sx_rat_cmp(c, a, b, &w->limits.arithmetic, &s);
    if (w->result.stats.comparisons < SIZE_MAX)
        w->result.stats.comparisons++;
    return numeric(w, e, s.reason);
}
static int import(Solve *w, SxRat *q, mpz_srcptr z) {
    SxStats s;
    SxError e = sx_rat_import(q, z, &w->limits.arithmetic, &s);
    if (e == SX_INVALID) {
        w->arithmetic_reason = s.reason;
        return stop(w, e, SX_REASON_INVALID_INPUT, SX_D_OBJECT);
    }
    return numeric(w, e, s.reason);
}
static int table_result(Solve *w, SxError e, const SxTableStats *s) {
    if (!e)
        return 1;
    if (w->scope.reason == SX_AR_TIME || w->scope.reason == SX_AR_CLOCK)
        return numeric(w, e, w->scope.reason);
    w->arithmetic_reason = s->arithmetic_reason;
    switch (s->reason) {
    case SX_T_TOTAL_BYTES:
        return stop(w, SX_LIMIT, SX_REASON_SPACE, SX_D_TOTAL_BYTES);
    case SX_T_ARITH_BYTES:
        return stop(w, SX_LIMIT, SX_REASON_ARITH_SPACE, SX_D_ARITH_BYTES);
    case SX_T_LIMBS:
        return stop(w, SX_LIMIT, SX_REASON_LIMBS, SX_D_LIMBS);
    case SX_T_OVERFLOW:
        return stop(w, SX_LIMIT, SX_REASON_SIZE_OVERFLOW, SX_D_OVERFLOW);
    case SX_T_ALLOC:
        return stop(w, SX_OOM, SX_REASON_ALLOCATION, SX_D_ALLOC);
    case SX_T_OBJECT:
        return stop(w, SX_INVALID, SX_REASON_INVALID_INPUT, SX_D_OBJECT);
    case SX_T_ARGUMENT:
    case SX_T_DIMENSION:
        return stop(w, SX_INVALID, SX_REASON_INVALID_INPUT, SX_D_ARGUMENT);
    case SX_T_REENTRY:
        return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_REENTRY);
    default:
        return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
    }
}
static int enabled(const Solve *w, unsigned int bit) {
    return !(w->limits.disable_optimizations & bit);
}
static void addstat(size_t *value, size_t n) {
    *value = n > SIZE_MAX - *value ? SIZE_MAX : *value + n;
}
static int one(const SxRat *q) {
    return q->num._mp_size == 1 && q->num._mp_d[0] == 1 && q->den._mp_size == 1 &&
           q->den._mp_d[0] == 1;
}
static void prepared_init(Prepared *p) {
    memset(p, 0, sizeof(*p));
    sx_rat_init(&p->unit);
    sx_rat_init(&p->contradiction);
    p->contradiction_row = SIZE_MAX;
}
static void prepared_coefficients_clear(Prepared *p) {
    for (size_t i = 0; i < p->coefficients_initialized; i++)
        sx_rat_clear(&p->coefficients[i]);
    sx_scope_free(p->coefficients);
    sx_scope_free(p->view);
    p->coefficients = NULL;
    p->view = NULL;
    p->coefficients_initialized = 0;
}
static void prepared_clear(Prepared *p) {
    prepared_coefficients_clear(p);
    for (size_t i = 0; i < p->scales_initialized; i++)
        sx_rat_clear(&p->scales[i]);
    sx_scope_free(p->scales);
    sx_scope_free(p->rowmap);
    sx_scope_free(p->colmap);
    sx_scope_free(p->used);
    sx_rat_clear(&p->unit);
    sx_rat_clear(&p->contradiction);
    prepared_init(p);
}
static void *array(Solve *w, size_t count, size_t element) {
    if (!count)
        return NULL;
    if (count > SIZE_MAX / element) {
        stop(w, SX_LIMIT, SX_REASON_SIZE_OVERFLOW, SX_D_OVERFLOW);
        return NULL;
    }
    void *p = sx_scope_alloc(count * element);
    if (!p)
        numeric(w, w->scope.error, w->scope.reason);
    return p;
}
static const SxRat *scale(const Prepared *p, size_t original_row) {
    return p->scales && p->scales[original_row].num._mp_size ? &p->scales[original_row] : &p->unit;
}
static int integer_op(Solve *w, SxRat *out, const SxRat *a, const SxRat *b, int gcd) {
    SxStats st;
    SxError e = gcd ? sx_integer_gcd(out, a, b, &w->limits.arithmetic, &st)
                    : sx_integer_divexact(out, a, b, &w->limits.arithmetic, &st);
    return numeric(w, e, st.reason);
}
static int prepare(Solve *w, const Source *source) {
    Prepared *p = &w->prep;
    p->enabled = 1;
    size_t m = source->rows, n = source->variables;
    unsigned int limb = 1;
    __mpz_struct unit = {0, 1, &limb};
    if (!import(w, &p->unit, &unit))
        return 0;
    p->rowmap = array(w, m, sizeof(size_t));
    if (m && !p->rowmap)
        return 0;
    p->colmap = array(w, n, sizeof(size_t));
    if (n && !p->colmap)
        return 0;
    if (enabled(w, SX_OPT_UNUSED_VARIABLES)) {
        p->used = array(w, n, 1);
        if (n && !p->used)
            return 0;
    }
    if (enabled(w, SX_OPT_ROW_GCD)) {
        p->scales = array(w, m, sizeof(SxRat));
        if (m && !p->scales)
            return 0;
        for (size_t i = 0; i < m; i++) {
            if (!checkpoint(w))
                return 0;
            sx_rat_init(&p->scales[i]);
            p->scales_initialized++;
        }
    }
    SxRat value, constant, g;
    sx_rat_init(&value);
    sx_rat_init(&constant);
    sx_rat_init(&g);
    int ok = 0;
    const struct InequList *node = source->head;
    /* Complete validation pass, even after a constant contradiction was found. */
    for (size_t i = 0; i < m; i++) {
        mpz_srcptr data = node->coef;
        int nonconstant = 0;
        sx_rat_clear(&g);
        for (size_t j = 0; j <= n; j++) {
            if (!checkpoint(w) || !import(w, &value, &data[j]))
                goto done;
            addstat(&w->result.stats.preprocess_coefficients_scanned, 1);
            if (!j) {
                if (!copy(w, &constant, &value))
                    goto done;
            } else if (value.num._mp_size) {
                nonconstant = 1;
                addstat(&w->result.stats.input_nonzeros, 1);
                if (p->used)
                    p->used[j - 1] = 1;
            }
            if (p->scales && value.num._mp_size && !one(&g))
                if (!integer_op(w, &g, &g, &value, 1))
                    goto done;
        }
        if (p->scales && g.num._mp_size && !one(&g))
            if (!copy(w, &p->scales[i], &g))
                goto done;
        if (!nonconstant && constant.num._mp_size > 0 && p->contradiction_row == SIZE_MAX) {
            p->contradiction_row = i;
            if (!copy(w, &p->contradiction, &constant))
                goto done;
        }
        if (!nonconstant && constant.num._mp_size <= 0 && enabled(w, SX_OPT_CONSTANT_ROWS))
            addstat(&w->result.stats.dropped_true_rows, 1);
        else
            p->rowmap[p->rows++] = i;
        node = node->next;
    }
    for (size_t j = 0; j < n; j++) {
        if (!checkpoint(w))
            goto done;
        if (!p->used || p->used[j])
            p->colmap[p->variables++] = j;
    }
    w->result.stats.active_rows = p->rows;
    w->result.stats.active_variables = p->variables;
    w->result.stats.removed_variables = n - p->variables;
    w->result.stats.active_nonzeros = w->result.stats.input_nonzeros;
    w->result.stats.active_cells = p->rows * p->variables;
    if (p->contradiction_row != SIZE_MAX && enabled(w, SX_OPT_CONSTANT_CONFLICT)) {
        ok = 1;
        goto done;
    }
    /* Identity transform: retain no maps or duplicate coefficient storage. */
    if (p->rows == m && p->variables == n) {
        int changed = 0;
        for (size_t i = 0; i < m; i++) {
            if (!checkpoint(w))
                goto done;
            if (!one(scale(p, i))) {
                changed = 1;
                break;
            }
        }
        if (!changed) {
            prepared_clear(p);
            ok = 1;
            goto done;
        }
    }
    if (p->variables == SIZE_MAX || p->rows > SIZE_MAX / (p->variables + 1)) {
        stop(w, SX_LIMIT, SX_REASON_SIZE_OVERFLOW, SX_D_OVERFLOW);
        goto done;
    }
    size_t count = p->rows * (p->variables + 1);
    p->coefficients = array(w, count, sizeof(SxRat));
    if (count && !p->coefficients)
        goto done;
    for (size_t i = 0; i < count; i++) {
        if (!checkpoint(w))
            goto done;
        sx_rat_init(&p->coefficients[i]);
        p->coefficients_initialized++;
    }
    p->view = array(w, count, sizeof(__mpz_struct));
    if (count && !p->view)
        goto done;
    node = source->head;
    size_t r = 0;
    /* A second linear source pass: no repeated list traversal or random lookup. */
    for (size_t i = 0; i < m; i++) {
        if (!checkpoint(w))
            goto done;
        if (r < p->rows && p->rowmap[r] == i) {
            mpz_srcptr data = node->coef;
            const SxRat *factor = scale(p, i);
            for (size_t j = 0; j <= p->variables; j++) {
                if (!checkpoint(w))
                    goto done;
                size_t source_column = j ? p->colmap[j - 1] + 1 : 0;
                size_t k = r * (p->variables + 1) + j;
                SxRat *q = &p->coefficients[k];
                if (!import(w, q, &data[source_column]))
                    goto done;
                if (!one(factor) && !integer_op(w, q, q, factor, 0))
                    goto done;
                p->view[k] = q->num;
            }
            if (!one(factor))
                addstat(&w->result.stats.gcd_reduced_rows, 1);
            r++;
        }
        node = node->next;
    }
    p->problem = (SxProblem){p->rows, p->variables, p->view};
    ok = 1;
done:
    sx_rat_clear(&value);
    sx_rat_clear(&constant);
    sx_rat_clear(&g);
    return ok;
}
static int constant_conflict(Solve *w, size_t original_variables) {
    SxConflict *c = &w->result.conflict;
    size_t row = w->prep.contradiction_row;
    c->row = row;
    c->basic_variable = original_variables + row;
    c->bound_source_row = row;
    c->to_lower = 0;
    if (!copy(w, &c->constant, &w->prep.contradiction) ||
        !copy(w, &c->attainable, &w->prep.contradiction) || !checkpoint(w))
        return 0;
    if (c->attainable.num._mp_size <= 0)
        return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
    c->present = 1;
    w->result.stats.constant_conflicts = 1;
    w->result.rational_status = SX_Q_UNSAT;
    w->result.integer_status = SX_Z_UNSAT;
    w->result.reason = SX_REASON_CONFLICT;
    return 1;
}
static int input_observe(Solve *w, const Source *source) {
    const struct InequList *node = source->head;
    for (size_t i = 0; i < source->rows; i++) {
        if (!checkpoint(w))
            return 0;
        mpz_srcptr data = node->coef;
        for (size_t j = 0; j < source->variables; j++)
            if (data[j + 1]._mp_size)
                addstat(&w->result.stats.input_nonzeros, 1);
        node = node->next;
    }
    w->result.stats.active_nonzeros = w->result.stats.input_nonzeros;
    return 1;
}
static size_t original_variable(const Solve *w, size_t variable, size_t original_n) {
    size_t n = w->prep.variables;
    return variable < n ? w->prep.colmap[variable] : original_n + w->prep.rowmap[variable - n];
}
static int remap_conflict(Solve *w, size_t original_n) {
    Prepared *p = &w->prep;
    if (!p->enabled)
        return 1;
    SxConflict *c = &w->result.conflict;
    size_t active_n = p->variables;
    const SxRat *left = c->basic_variable >= active_n
                            ? scale(p, p->rowmap[c->basic_variable - active_n])
                            : &p->unit;
    for (size_t i = 0; i < c->blocker_count; i++) {
        if (!checkpoint(w))
            return 0;
        SxBlocker *b = &c->blockers[i];
        const SxRat *right =
            b->variable >= active_n ? scale(p, p->rowmap[b->variable - active_n]) : &p->unit;
        if (!one(left) && !op(w, &b->coefficient, '*', &b->coefficient, left))
            return 0;
        if (!one(right) && (!op(w, &b->coefficient, '/', &b->coefficient, right) ||
                            !op(w, &b->bound, '*', &b->bound, right)))
            return 0;
        b->variable = original_variable(w, b->variable, original_n);
        if (b->source_row != SIZE_MAX)
            b->source_row = p->rowmap[b->source_row];
    }
    if (!one(left) && (!op(w, &c->constant, '*', &c->constant, left) ||
                       !op(w, &c->required, '*', &c->required, left) ||
                       !op(w, &c->attainable, '*', &c->attainable, left)))
        return 0;
    c->row = p->rowmap[c->row];
    c->basic_variable = original_variable(w, c->basic_variable, original_n);
    if (c->bound_source_row != SIZE_MAX)
        c->bound_source_row = p->rowmap[c->bound_source_row];
    SxRat sum, term;
    sx_rat_init(&sum);
    sx_rat_init(&term);
    int ok = copy(w, &sum, &c->constant), cmp = 0;
    for (size_t i = 0; ok && i < c->blocker_count; i++)
        ok = op(w, &term, '*', &c->blockers[i].coefficient, &c->blockers[i].bound) &&
             op(w, &sum, '+', &sum, &term);
    if (ok)
        ok = compare(w, &sum, &c->attainable, &cmp);
    if (ok && cmp)
        ok = stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
    if (ok)
        ok = compare(w, &c->attainable, &c->required, &cmp);
    if (ok && ((c->to_lower && cmp >= 0) || (!c->to_lower && cmp <= 0)))
        ok = stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
    sx_rat_clear(&sum);
    sx_rat_clear(&term);
    return ok;
}
static int violated(Solve *w, size_t *row, int *lower) {
    size_t n = sx_table_variables(w->table);
    *row = SIZE_MAX;
    for (size_t v = 0; v < n; v++) {
        if (!checkpoint(w))
            return 0;
        size_t r = sx_table_basic_row(w->table, v);
        if (r == SIZE_MAX)
            continue;
        const SxRat *x = sx_table_value(w->table, v), *lo = sx_table_lower(w->table, v),
                    *hi = sx_table_upper(w->table, v);
        int c;
        if (lo) {
            if (!compare(w, x, lo, &c))
                return 0;
            if (c < 0) {
                *row = r;
                *lower = 1;
                return 1;
            }
        }
        if (hi) {
            if (!compare(w, x, hi, &c))
                return 0;
            if (c > 0) {
                *row = r;
                *lower = 0;
                return 1;
            }
        }
    }
    return 1;
}
static int entering(Solve *w, size_t row, int lower, size_t *out) {
    *out = SIZE_MAX;
    size_t n = sx_table_variables(w->table);
    for (size_t v = 0; v < n; v++) {
        if (!checkpoint(w))
            return 0;
        if (sx_table_nonbasic_column(w->table, v) == SIZE_MAX)
            continue;
        const SxRat *a = sx_table_coefficient(w->table, row, v);
        int sign = a->num._mp_size;
        if (!sign)
            continue;
        int up = lower ? (sign > 0) : (sign < 0);
        const SxRat *b = up ? sx_table_upper(w->table, v) : sx_table_lower(w->table, v);
        if (!b) {
            *out = v;
            return 1;
        }
        int c;
        if (!compare(w, sx_table_value(w->table, v), b, &c))
            return 0;
        if ((up && c < 0) || (!up && c > 0)) {
            *out = v;
            return 1;
        }
        if ((up && c > 0) || (!up && c < 0))
            return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
    }
    return 1;
}
static size_t source(const Solve *w, size_t variable) {
    size_t n = sx_table_original_variables(w->table), m = sx_table_rows(w->table);
    return variable >= n && variable - n < m ? variable - n : SIZE_MAX;
}
static int conflict(Solve *w, size_t row, int lower, size_t original_n) {
    SxConflict *c = &w->result.conflict;
    size_t n = sx_table_variables(w->table), count = 0;
    for (size_t v = 0; v < n; v++)
        if (sx_table_nonbasic_column(w->table, v) != SIZE_MAX &&
            sx_table_coefficient(w->table, row, v)->num._mp_size)
            count++;
    c->blockers = array(w, count, sizeof(*c->blockers));
    if (count && !c->blockers)
        return 0;
    c->row = row;
    c->basic_variable = sx_table_basic(w->table, row);
    c->bound_source_row = source(w, c->basic_variable);
    c->to_lower = lower;
    const SxRat *required = lower ? sx_table_lower(w->table, c->basic_variable)
                                  : sx_table_upper(w->table, c->basic_variable);
    if (!required)
        return stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
    if (!copy(w, &c->required, required) || !copy(w, &c->constant, sx_table_beta(w->table, row)) ||
        !copy(w, &c->attainable, &c->constant))
        return 0;
    SxRat p;
    sx_rat_init(&p);
    int ok = 0;
    for (size_t v = 0; v < n; v++) {
        if (!checkpoint(w))
            goto done;
        if (sx_table_nonbasic_column(w->table, v) == SIZE_MAX)
            continue;
        const SxRat *a = sx_table_coefficient(w->table, row, v);
        if (!a->num._mp_size)
            continue;
        int maximize = lower, is_lower = maximize ? (a->num._mp_size < 0) : (a->num._mp_size > 0);
        const SxRat *b = is_lower ? sx_table_lower(w->table, v) : sx_table_upper(w->table, v);
        int cmp;
        if (!b) {
            stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
            goto done;
        }
        if (!compare(w, sx_table_value(w->table, v), b, &cmp))
            goto done;
        if (cmp) {
            stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
            goto done;
        }
        SxBlocker *term = &c->blockers[c->blocker_count];
        sx_rat_init(&term->coefficient);
        sx_rat_init(&term->bound);
        c->blocker_count++;
        term->variable = v;
        term->source_row = source(w, v);
        term->is_lower = is_lower;
        if (!copy(w, &term->coefficient, a) || !copy(w, &term->bound, b) || !op(w, &p, '*', a, b) ||
            !op(w, &c->attainable, '+', &c->attainable, &p))
            goto done;
    }
    {
        int cmp;
        if (!compare(w, &c->attainable, &c->required, &cmp))
            goto done;
        if ((lower && cmp >= 0) || (!lower && cmp <= 0)) {
            stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
            goto done;
        }
    }
    if (!checkpoint(w))
        goto done;
    if (!remap_conflict(w, original_n) || !checkpoint(w))
        goto done;
    c->present = 1;
    w->result.stats.conflict_terms = c->blocker_count;
    ok = 1;
done:
    sx_rat_clear(&p);
    return ok;
}
static int feasible(Solve *w, const Source *p) {
    size_t n = p->variables;
    w->result.witness = array(w, n, sizeof(*w->result.witness));
    if (n && !w->result.witness)
        return 0;
    int integral = 1;
    size_t active_column = 0;
    for (size_t v = 0; v < n; v++) {
        if (!checkpoint(w))
            return 0;
        SxRat *q = &w->result.witness[v];
        sx_rat_init(q);
        w->result.witness_length++;
        if (!w->prep.enabled) {
            if (!copy(w, q, sx_table_value(w->table, v)))
                return 0;
        } else if (active_column < w->prep.variables && w->prep.colmap[active_column] == v) {
            if (!copy(w, q, sx_table_value(w->table, active_column)))
                return 0;
            active_column++;
        }
        if (q->den._mp_size != 1 || q->den._mp_d[0] != 1)
            integral = 0;
    }
    SxRat sum, a, product;
    sx_rat_init(&sum);
    sx_rat_init(&a);
    sx_rat_init(&product);
    int ok = 0;
    const struct InequList *node = p->head;
    for (size_t i = 0; i < p->rows; i++) {
        mpz_srcptr data = node->coef;
        if (!checkpoint(w) || !import(w, &sum, data))
            goto done;
        for (size_t j = 0; j < n; j++) {
            if (!checkpoint(w))
                goto done;
            if (!data[j + 1]._mp_size) {
                addstat(&w->result.stats.verification_coefficients_skipped, 1);
                continue;
            }
            if (!import(w, &a, &data[j + 1]) || !op(w, &product, '*', &a, &w->result.witness[j]) ||
                !op(w, &sum, '+', &sum, &product))
                goto done;
        }
        if (sum.num._mp_size > 0) {
            stop(w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_INVARIANT);
            goto done;
        }
        w->result.stats.verified_rows++;
        node = node->next;
    }
    if (!checkpoint(w))
        goto done;
    w->result.rational_status = SX_Q_FEASIBLE;
    w->result.integer_status = integral ? SX_Z_SAT : SX_Z_UNKNOWN;
    w->result.reason = integral ? SX_REASON_NONE : SX_REASON_FRACTIONAL;
    ok = 1;
done:
    sx_rat_clear(&sum);
    sx_rat_clear(&a);
    sx_rat_clear(&product);
    return ok;
}
static int dimensions(Solve *w, size_t m, size_t n) {
    if (n == SIZE_MAX || m > SIZE_MAX / (n + 1) || m * (n + 1) > SIZE_MAX / sizeof(__mpz_struct) ||
        n > SIZE_MAX - m)
        return stop(w, SX_LIMIT, SX_REASON_SIZE_OVERFLOW, SX_D_OVERFLOW);
    return 1;
}
static int source_validate(Solve *w, Source *p) {
    if (!dimensions(w, 0, p->variables))
        return 0;
    const struct InequList *slow = p->head, *fast = p->head;
    while (fast && fast->next) {
        if (!checkpoint(w))
            return 0;
        slow = slow->next;
        fast = fast->next->next;
        if (slow == fast)
            return stop(w, SX_INVALID, SX_REASON_INVALID_INPUT, SX_D_CYCLE);
    }
    for (const struct InequList *node = p->head; node; node = node->next) {
        if (!checkpoint(w))
            return 0;
        if (!node->coef)
            return stop(w, SX_INVALID, SX_REASON_INVALID_INPUT, SX_D_OBJECT);
        if (p->rows == SIZE_MAX)
            return stop(w, SX_LIMIT, SX_REASON_SIZE_OVERFLOW, SX_D_OVERFLOW);
        p->rows++;
    }
    return dimensions(w, p->rows, p->variables);
}
static int validate_limits(Solve *w) {
    if (w->limits.disable_optimizations & ~(unsigned int)SX_OPT_ALL)
        return stop(w, SX_INVALID, SX_REASON_INVALID_INPUT, SX_D_ARGUMENT);
    size_t limbs = w->limits.arithmetic.max_limbs;
    if ((limbs && (limbs < 4 || limbs > (size_t)INT_MAX / 64)) || w->limits.arithmetic.fail_at)
        return stop(w, SX_INVALID, SX_REASON_INVALID_INPUT, SX_D_ARGUMENT);
    return 1;
}
void sx_check_qcp(const struct InequList *head, size_t variables, const SxSolverLimits *l,
                  SxResult *out) {
    Source source = {head, 0, variables};
    if (!out)
        return;
    Solve w;
    memset(&w, 0, sizeof(w));
    sx_result_init(&w.result);
    prepared_init(&w.prep);
    if (l)
        w.limits = *l;
    if (!w.limits.max_table_bytes)
        w.limits.max_table_bytes = 256 * 1024 * 1024;
    if (!w.limits.max_pivots)
        w.limits.max_pivots = 100000;
    if (!w.limits.max_milliseconds)
        w.limits.max_milliseconds = 10000;
    if (solving) {
        stop(&w, SX_INTERNAL, SX_REASON_INTERNAL, SX_D_REENTRY);
        goto publish;
    }
    if (!validate_limits(&w))
        goto publish;
    {
        SxError e = sx_scope_begin(&w.scope, 0, w.limits.max_table_bytes, w.limits.fail_at);
        if (e) {
            numeric(&w, e, w.scope.reason);
            goto publish;
        }
    }
    solving = 1;
    w.scope.allow_children = 1;
    if (sx_scope_deadline(&w.scope, w.limits.max_milliseconds) != SX_OK) {
        numeric(&w, w.scope.error, w.scope.reason);
        goto done;
    }
    if (!source_validate(&w, &source))
        goto done;
    w.result.stats.input_rows = source.rows;
    w.result.stats.input_variables = source.variables;
    w.result.stats.active_rows = source.rows;
    w.result.stats.active_variables = source.variables;
    w.result.stats.input_cells = source.rows * source.variables;
    w.result.stats.active_cells = w.result.stats.input_cells;
    const int preprocess = w.limits.disable_optimizations != SX_OPT_ALL;
    if (preprocess) {
        if (!prepare(&w, &source))
            goto done;
        if (w.prep.contradiction_row != SIZE_MAX && enabled(&w, SX_OPT_CONSTANT_CONFLICT)) {
            constant_conflict(&w, source.variables);
            goto done;
        }
    }
    const SxTableLimits tl = {
        .arithmetic = w.limits.arithmetic,
        .max_table_bytes = w.limits.max_table_bytes,
    };
    {
        SxTableStats ts;
        SxError e = w.prep.enabled ? sx_table_create(&w.table, &w.prep.problem, &tl, &ts)
                    : sx_table_create_validated_list(&w.table, source.head, source.rows,
                                                     source.variables, &tl, &ts);
        if (!table_result(&w, e, &ts))
            goto done;
    }
    prepared_coefficients_clear(&w.prep);
    if (!preprocess && !input_observe(&w, &source))
        goto done;
    while (checkpoint(&w)) {
        size_t row, enter;
        int lower = 0;
        if (!violated(&w, &row, &lower))
            goto done;
        if (row == SIZE_MAX) {
            feasible(&w, &source);
            goto done;
        }
        if (!entering(&w, row, lower, &enter))
            goto done;
        if (enter == SIZE_MAX) {
            if (conflict(&w, row, lower, source.variables)) {
                w.result.rational_status = SX_Q_UNSAT;
                w.result.integer_status = SX_Z_UNSAT;
                w.result.reason = SX_REASON_CONFLICT;
            }
            goto done;
        }
        if (w.result.stats.pivots >= w.limits.max_pivots) {
            stop(&w, SX_LIMIT, SX_REASON_PIVOTS, SX_D_PIVOTS);
            goto done;
        }
        {
            SxTableStats ts;
            SxError e = sx_table_pivot(&w.table, row, enter, lower, &tl, &ts);
            if (!table_result(&w, e, &ts))
                goto done;
        }
        w.result.stats.pivots++;
    }
done:
    sx_table_destroy(w.table);
    w.table = NULL;
    prepared_clear(&w.prep);
    if (!w.error)
        checkpoint(&w);
    w.result.stats.allocations = w.scope.attempts;
    w.result.stats.peak_bytes = w.scope.peak;
    sx_scope_end(&w.scope);
    solving = 0;
publish:
    if (w.error) {
        SxSolverStats stats = w.result.stats;
        sx_result_clear(&w.result);
        w.result.stats = stats;
        w.result.reason = w.reason;
        w.result.diagnostic = w.diagnostic;
        w.result.arithmetic_reason = w.arithmetic_reason;
        if (w.error == SX_LIMIT) {
            w.result.error = SX_OK;
            w.result.rational_status = SX_Q_UNKNOWN;
            w.result.integer_status = SX_Z_UNKNOWN;
        } else
            w.result.error = w.error;
    }
    *out = w.result;
}

