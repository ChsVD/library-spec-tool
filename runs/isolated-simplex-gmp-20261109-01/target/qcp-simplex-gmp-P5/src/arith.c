#define _POSIX_C_SOURCE 200809L
#include "backend.h"
#include "runtime_scope.h"
#include <time.h>
_Static_assert(UINT_MAX == 4294967295U, "requires 32-bit unsigned int limbs");
typedef union Block Block;
union Block {
    max_align_t align;
    struct {
        Block *prev, *next;
        size_t bytes;
        int attached;
    } h;
};
typedef struct {
    jmp_buf jump;
    Block *head;
    size_t live, peak, attempt, maxbytes, maxlimbs, fail;
    SxError error;
    SxArithReason reason;
} Tx;
static _Thread_local Tx *active;
static _Thread_local size_t live_blocks;
static unsigned int one = 1;
static _Thread_local size_t owned_bytes;
static _Thread_local SxScope *scope;
typedef union {
    max_align_t align;
    size_t bytes;
} Storage;
void sx_scope_work(SxWorkKind kind, size_t limbs) {
    for (SxScope *s = scope; s; s = s->parent) {
        size_t *counter = NULL;
        switch (kind) {
        case SX_W_ADD:
            counter = &s->work.rat_add;
            break;
        case SX_W_SUB:
            counter = &s->work.rat_sub;
            break;
        case SX_W_MUL:
            counter = &s->work.rat_mul;
            break;
        case SX_W_DIV:
            counter = &s->work.rat_div;
            break;
        case SX_W_CMP:
            counter = &s->work.rat_compare;
            break;
        case SX_W_IMPORT:
            counter = &s->work.rat_import;
            break;
        case SX_W_BIG_ADD:
            counter = &s->work.big_add;
            break;
        case SX_W_BIG_SUB:
            counter = &s->work.big_sub;
            break;
        case SX_W_BIG_MUL:
            counter = &s->work.big_mul;
            break;
        case SX_W_BIG_GCD:
            counter = &s->work.big_gcd;
            break;
        case SX_W_BIG_DIVEXACT:
            counter = &s->work.big_divexact;
            break;
        }
        if (counter && *counter < SIZE_MAX)
            ++*counter;
        if (limbs > s->work.max_operand_limbs)
            s->work.max_operand_limbs = limbs;
    }
}
static SxError clock_ms(unsigned long long *out) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0 || now.tv_sec < 0)
        return SX_INTERNAL;
    unsigned long long sec = (unsigned long long)now.tv_sec;
    if (sec > ULLONG_MAX / 1000) {
        *out = ULLONG_MAX;
        return SX_OK;
    }
    unsigned long long base = sec * 1000, fraction = (unsigned long long)now.tv_nsec / 1000000;
    *out = fraction > ULLONG_MAX - base ? ULLONG_MAX : base + fraction;
    return SX_OK;
}
SxError sx_scope_deadline(SxScope *s, unsigned long long ms) {
    if (clock_ms(&s->started_ms) != SX_OK) {
        s->error = SX_INTERNAL;
        s->reason = SX_AR_CLOCK;
        return SX_INTERNAL;
    }
    s->duration_ms = ms;
    return SX_OK;
}
SxError sx_scope_checkpoint(void) {
    for (SxScope *s = scope; s; s = s->parent)
        if (s->duration_ms) {
            unsigned long long now;
            SxError e = clock_ms(&now);
            if (e != SX_OK || now < s->started_ms || now - s->started_ms >= s->duration_ms) {
                s->error = e == SX_OK && now >= s->started_ms ? SX_LIMIT : SX_INTERNAL;
                s->reason = s->error == SX_LIMIT ? SX_AR_TIME : SX_AR_CLOCK;
                if (scope) {
                    scope->error = s->error;
                    scope->reason = s->reason;
                }
                return s->error;
            }
        }
    return SX_OK;
}
static SxError scope_charge(size_t n) {
    if (sx_scope_checkpoint() != SX_OK)
        return scope->error;
    for (SxScope *s = scope; s; s = s->parent) {
        s->attempts++;
        size_t delta = owned_bytes - s->baseline;
        SxError e = SX_OK;
        SxArithReason reason = SX_AR_NONE;
        if (delta > SIZE_MAX - s->initial || n > SIZE_MAX - delta - s->initial) {
            e = SX_LIMIT;
            reason = SX_AR_SIZE_OVERFLOW;
        } else if (s->initial + delta + n > s->limit) {
            e = SX_LIMIT;
            reason = SX_AR_BYTES;
        } else if (s->fail && s->attempts == s->fail) {
            e = SX_OOM;
            reason = SX_AR_ALLOC;
        }
        if (e) {
            s->error = e;
            s->reason = reason;
            scope->error = e;
            scope->reason = reason;
            return e;
        }
        size_t next = s->initial + delta + n;
        if (next > s->peak)
            s->peak = next;
    }
    return SX_OK;
}
SxError sx_scope_begin(SxScope *s, size_t initial, size_t limit, size_t fail) {
    memset(s, 0, sizeof(*s));
    if ((scope && !scope->allow_children) || active) {
        s->reason = SX_AR_REENTRY;
        return SX_INTERNAL;
    }
    s->baseline = owned_bytes;
    s->initial = initial;
    s->limit = limit;
    s->peak = initial;
    s->fail = fail;
    if (initial > limit) {
        s->reason = SX_AR_BYTES;
        return SX_LIMIT;
    }
    s->parent = scope;
    scope = s;
    return SX_OK;
}
void sx_scope_end(SxScope *s) {
    if (scope == s)
        scope = s->parent;
}
void *sx_scope_alloc(size_t n) {
    if (n > SIZE_MAX - sizeof(Storage)) {
        if (scope) {
            scope->error = SX_LIMIT;
            scope->reason = SX_AR_SIZE_OVERFLOW;
        }
        return NULL;
    }
    size_t bytes = n + sizeof(Storage);
    if (scope_charge(bytes) != SX_OK)
        return NULL;
    Storage *p = calloc(1, bytes);
    if (!p) {
        if (scope) {
            scope->error = SX_OOM;
            scope->reason = SX_AR_ALLOC;
        }
        return NULL;
    }
    p->bytes = bytes;
    owned_bytes += bytes;
    return p + 1;
}
void sx_scope_free(void *p) {
    if (p) {
        Storage *h = (Storage *)p - 1;
        owned_bytes -= h->bytes;
        free(h);
    }
}
size_t sx_scope_size(const void *p) {
    return p ? ((const Storage *)p - 1)->bytes : 0;
}
size_t sx_rat_bytes(const SxRat *q) {
    return (q->num._mp_alloc ? sizeof(Block) + (size_t)q->num._mp_alloc * sizeof(unsigned int)
                             : 0) +
           (q->den._mp_alloc ? sizeof(Block) + (size_t)q->den._mp_alloc * sizeof(unsigned int) : 0);
}

static void die(SxError e, SxArithReason reason) {
    if (!active)
        abort();
    active->error = e;
    active->reason = reason;
    longjmp(active->jump, 1);
}
static void detach(Block *b) {
    if (!b->h.attached)
        return;
    if (b->h.prev)
        b->h.prev->h.next = b->h.next;
    else
        active->head = b->h.next;
    if (b->h.next)
        b->h.next->h.prev = b->h.prev;
    active->live -= b->h.bytes;
    b->h.attached = 0;
    b->h.prev = b->h.next = NULL;
}
static void release(void *p) {
    if (!p)
        return;
    Block *b = (Block *)p - 1;
    detach(b);
    --live_blocks;
    owned_bytes -= sizeof(Block) + b->h.bytes;
    free(b);
}
static void *allocate(size_t n) {
    Tx *t = active;
    if (!t)
        abort();
    ++t->attempt;
    if (n > SIZE_MAX - sizeof(Block))
        die(SX_LIMIT, SX_AR_SIZE_OVERFLOW);
    if (n > t->maxbytes - t->live)
        die(SX_LIMIT, SX_AR_BYTES);
    if (t->fail && t->attempt == t->fail)
        die(SX_OOM, SX_AR_ALLOC);
    if (scope_charge(sizeof(Block) + n) != SX_OK)
        die(scope->error, scope->reason);
    Block *b = malloc(sizeof(Block) + n);
    if (!b)
        die(SX_OOM, SX_AR_ALLOC);
    b->h.prev = NULL;
    b->h.next = t->head;
    b->h.bytes = n;
    b->h.attached = 1;
    if (t->head)
        t->head->h.prev = b;
    t->head = b;
    t->live += n;
    if (t->live > t->peak)
        t->peak = t->live;
    ++live_blocks;
    owned_bytes += sizeof(Block) + n;
    return b + 1;
}
unsigned int *gmp_alloc_limbs(int n) {
    if (n < 1 || (size_t)n > active->maxlimbs)
        die(SX_LIMIT, SX_AR_LIMBS);
    return allocate((size_t)n * sizeof(unsigned int));
}
void gmp_free_limbs(unsigned int *p, int n) {
    (void)n;
    release(p);
}
unsigned int *gmp_realloc_limbs(unsigned int *p, int old, int n) {
    unsigned int *q = gmp_alloc_limbs(n);
    memcpy(q, p, (size_t)(old < n ? old : n) * sizeof(*q));
    release(p);
    return q;
}
mpz_ptr malloc_mpz_struct(void) {
    return allocate(sizeof(__mpz_struct));
}
void free_mpz_struct(mpz_ptr p) {
    release(p);
}
struct gmp_div_inverse *malloc_gmp_div_inverse(void) {
    return allocate(sizeof(struct gmp_div_inverse));
}
void free_gmp_div_inverse(struct gmp_div_inverse *p) {
    release(p);
}
void int_swap(int *a, int *b) {
    int t = *a;
    *a = *b;
    *b = t;
}
void mp_ptr_swap(unsigned int **a, unsigned int **b) {
    unsigned int *t = *a;
    *a = *b;
    *b = t;
}
void mpz_srcptr_swap(mpz_srcptr *a, mpz_srcptr *b) {
    mpz_srcptr t = *a;
    *a = *b;
    *b = t;
}
int mpn_zero_p(unsigned int *p, int n) {
    for (int i = 0; i < n; i++)
        if (p[i])
            return 0;
    return 1;
}
size_t sx_runtime_live_bytes(void) {
    return owned_bytes;
}
size_t sx_live_blocks(void) {
    return live_blocks;
}
void sx_rat_init(SxRat *q) {
    mpz_init(&q->num);
    mpz_init(&q->den);
    q->den._mp_size = 1;
    q->den._mp_d = &one;
}
static void zclear(mpz_ptr z) {
    if (z->_mp_alloc)
        release(z->_mp_d);
    mpz_init(z);
}
void sx_rat_clear(SxRat *q) {
    zclear(&q->num);
    zclear(&q->den);
    sx_rat_init(q);
}
void sx_string_free(char *p) {
    release(p);
}
static size_t length(mpz_srcptr z) {
    return (size_t)(z->_mp_size < 0 ? -z->_mp_size : z->_mp_size);
}
static void bound(size_t n) {
    if (n > active->maxlimbs)
        die(SX_LIMIT, SX_AR_LIMBS);
}
static void mul(mpz_ptr z, mpz_srcptr a, mpz_srcptr b) {
    bound(length(a) + length(b));
    sx_scope_work(SX_W_BIG_MUL, length(a) > length(b) ? length(a) : length(b));
    mpz_mul(z, a, b);
}
static void add(mpz_ptr z, mpz_srcptr a, mpz_srcptr b, int sub) {
    size_t x = length(a), y = length(b);
    bound((x > y ? x : y) + 1);
    sx_scope_work(sub ? SX_W_BIG_SUB : SX_W_BIG_ADD, x > y ? x : y);
    if (sub)
        mpz_sub(z, a, b);
    else
        mpz_add(z, a, b);
}
static void gcd(mpz_ptr z, mpz_srcptr a, mpz_srcptr b) {
    size_t x = length(a), y = length(b);
    bound((x > y ? x : y) + 2);
    sx_scope_work(SX_W_BIG_GCD, x > y ? x : y);
    mpz_gcd(z, a, b);
}
static void divexact(mpz_ptr z, mpz_srcptr a, mpz_srcptr b) {
    if (!b->_mp_size)
        die(SX_INTERNAL, SX_AR_BAD_ARGUMENT);
    bound(length(a) + 1);
    sx_scope_work(SX_W_BIG_DIVEXACT, length(a) > length(b) ? length(a) : length(b));
    mpz_divexact(z, a, b);
}
static void parse(mpz_ptr z, const char *s) {
    z->_mp_size = 0;
    if (!s || !*s)
        die(SX_INVALID, SX_AR_BAD_DECIMAL);
    int neg = 0;
    if (*s == '-' || *s == '+') {
        neg = *s == '-';
        ++s;
    }
    if (!*s)
        die(SX_INVALID, SX_AR_BAD_DECIMAL);
    __mpz_struct ten, digit;
    mpz_init(&ten);
    mpz_init(&digit);
    mpz_set_ui(&ten, 10);
    for (; *s; s++) {
        if (*s < '0' || *s > '9')
            die(SX_INVALID, SX_AR_BAD_DECIMAL);
        mpz_set_ui(&digit, (unsigned)(*s - '0'));
        mul(z, z, &ten);
        add(z, z, &digit, 0);
    }
    if (neg)
        mpz_neg(z, z);
}
static void normalize(SxRat *q) {
    if (!q->den._mp_size)
        die(SX_INVALID, SX_AR_ZERO_DENOMINATOR);
    if (q->den._mp_size < 0) {
        mpz_neg(&q->num, &q->num);
        mpz_neg(&q->den, &q->den);
    }
    if (!q->num._mp_size) {
        mpz_set_ui(&q->den, 1);
        return;
    }
    __mpz_struct g;
    mpz_init(&g);
    gcd(&g, &q->num, &q->den);
    divexact(&q->num, &q->num, &g);
    divexact(&q->den, &q->den, &g);
}
/* Cross cancellation before products. Addition uses denominator gcd. */
static void calculate(SxRat *q, char op, const SxRat *a, const SxRat *b) {
    if (op == '/' && !b->num._mp_size)
        die(SX_INVALID, SX_AR_DIV_ZERO);
    if ((op == '*' || op == '/') && !a->num._mp_size)
        return;
    if (op == '*' && !b->num._mp_size)
        return;
    if ((op == '+' || op == '-') && !b->num._mp_size) {
        bound(length(&a->num));
        bound(length(&a->den));
        mpz_set(&q->num, &a->num);
        mpz_set(&q->den, &a->den);
        return;
    }
    if ((op == '+' || op == '-') && !a->num._mp_size) {
        bound(length(&b->num));
        bound(length(&b->den));
        mpz_set(&q->num, &b->num);
        mpz_set(&q->den, &b->den);
        if (op == '-')
            mpz_neg(&q->num, &q->num);
        return;
    }

    __mpz_struct g, h, x, y, u, v;
    mpz_init(&g);
    mpz_init(&h);
    mpz_init(&x);
    mpz_init(&y);
    mpz_init(&u);
    mpz_init(&v);
    if (op == '+' || op == '-') {
        gcd(&g, &a->den, &b->den);
        divexact(&x, &a->den, &g);
        divexact(&y, &b->den, &g);
        mul(&u, &a->num, &y);
        mul(&v, &b->num, &x);
        add(&q->num, &u, &v, op == '-');
        mul(&q->den, &x, &b->den);
    } else if (op == '*' || op == '/') {
        mpz_srcptr bn = op == '*' ? &b->num : &b->den, bd = op == '*' ? &b->den : &b->num;
        if (!bd->_mp_size)
            die(SX_INVALID, SX_AR_DIV_ZERO);
        gcd(&g, &a->num, bd);
        gcd(&h, bn, &a->den);
        divexact(&x, &a->num, &g);
        divexact(&y, bn, &h);
        mul(&q->num, &x, &y);
        divexact(&x, &a->den, &h);
        divexact(&y, bd, &g);
        mul(&q->den, &x, &y);
    } else
        die(SX_INVALID, SX_AR_BAD_DECIMAL);
    normalize(q);
}
static char *decimal(mpz_srcptr z) {
    size_t n = length(z);
    bound(n);
    if (n > (SIZE_MAX - 3) / 10)
        die(SX_LIMIT, SX_AR_SIZE_OVERFLOW);
    size_t cap = n * 10 + 3;
    char *s = allocate(cap);
    unsigned int *p = allocate((n ? n : 1) * sizeof(*p));
    if (n)
        memcpy(p, z->_mp_d, n * sizeof(*p));
    size_t used = 0;
    do {
        uint64_t rem = 0;
        for (size_t i = n; i > 0; i--) {
            uint64_t v = (rem << 32) | p[i - 1];
            p[i - 1] = (unsigned int)(v / 10);
            rem = v % 10;
        }
        s[used++] = (char)('0' + rem);
        while (n && p[n - 1] == 0)
            n--;
    } while (n);
    if (z->_mp_size < 0)
        s[used++] = '-';
    s[used] = 0;
    for (size_t i = 0; i < used / 2; i++) {
        char c = s[i];
        s[i] = s[used - i - 1];
        s[used - i - 1] = c;
    }
    return s;
}
static int valid(const SxRat *q) {
    return q && q->den._mp_size > 0 && q->num._mp_size != INT_MIN && q->den._mp_size != INT_MIN;
}
static SxError early(SxStats *stats, SxError error, SxArithReason reason) {
    if (stats) {
        memset(stats, 0, sizeof(*stats));
        stats->reason = reason;
    }
    return error;
}
/* Heap transaction remains defined after longjmp. No mutated automatic is read
   on the jump branch; all persistent outputs are touched after success only. */
static SxError run(SxRat *out, int *cmp, char **str, char op, const SxRat *a, const SxRat *b,
                   const char *ns, const char *ds, mpz_srcptr imported, const SxLimits *l,
                   SxStats *stats) {
    if (stats)
        memset(stats, 0, sizeof(*stats));
    if (active)
        return early(stats, SX_INTERNAL, SX_AR_REENTRY);
    if (((op == 's' || op == 'i') && !out) || (op != 's' && op != 'i' && !valid(a)) ||
        ((op == '+' || op == '-' || op == '*' || op == '/' || op == 'c' || op == 'g' ||
          op == 'x') &&
         !valid(b)))
        return early(stats, SX_INVALID, SX_AR_BAD_ARGUMENT);
    switch (op) {
    case '+':
        sx_scope_work(SX_W_ADD, 0);
        break;
    case '-':
        sx_scope_work(SX_W_SUB, 0);
        break;
    case '*':
        sx_scope_work(SX_W_MUL, 0);
        break;
    case '/':
        sx_scope_work(SX_W_DIV, 0);
        break;
    case 'c':
        sx_scope_work(SX_W_CMP, 0);
        break;
    case 'i':
        sx_scope_work(SX_W_IMPORT, length(imported));
        break;
    default:
        break;
    }
    size_t max = l && l->max_limbs ? l->max_limbs : 1048576;
    if (max > (size_t)INT_MAX / 64 || max < 4)
        return early(stats, SX_INVALID, SX_AR_BAD_ARGUMENT);
    if (l && l->fail_at == 1) {
        if (stats)
            stats->allocations = 1;
        if (stats)
            stats->reason = SX_AR_ALLOC;
        return SX_OOM;
    }
    if (scope_charge(sizeof(Tx)) != SX_OK)
        return early(stats, scope->error, scope->reason);
    Tx *volatile t = calloc(1, sizeof(*t));
    if (!t) {
        early(stats, SX_OOM, SX_AR_ALLOC);
        if (stats)
            stats->allocations = 1;
        return SX_OOM;
    }
    owned_bytes += sizeof(Tx);
    t->attempt = 1;
    t->maxlimbs = max;
    t->maxbytes = l && l->max_bytes ? l->max_bytes : 64 * 1024 * 1024;
    t->fail = l ? l->fail_at : 0;
    active = t;
    if (setjmp(t->jump) == 0) {
        if (op == 'c') {
            __mpz_struct x, y;
            mpz_init(&x);
            mpz_init(&y);
            mul(&x, &a->num, &b->den);
            mul(&y, &b->num, &a->den);
            *cmp = mpz_cmp(&x, &y);
        } else if (op == 'e') {
            char *n = decimal(&a->num), *d = decimal(&a->den);
            size_t nn = strlen(n), dn = strlen(d);
            if (nn > SIZE_MAX - dn - 2)
                die(SX_LIMIT, SX_AR_SIZE_OVERFLOW);
            char *p = allocate(nn + dn + 2);
            memcpy(p, n, nn);
            p[nn] = '/';
            memcpy(p + nn + 1, d, dn + 1);
            detach((Block *)p - 1);
            *str = p;
        } else {
            SxRat q;
            sx_rat_init(&q);
            if (op == 'g') {
                gcd(&q.num, &a->num, &b->num);
            } else if (op == 'x') {
                divexact(&q.num, &a->num, &b->num);
            } else if (op == 'i') {
                bound(length(imported));
                mpz_set(&q.num, imported);
            } else if (op == 's') {
                parse(&q.num, ns);
                parse(&q.den, ds);
                normalize(&q);
            } else
                calculate(&q, op, a, b);
            if (q.num._mp_alloc)
                detach((Block *)q.num._mp_d - 1);
            if (q.den._mp_alloc)
                detach((Block *)q.den._mp_d - 1);
            sx_rat_clear(out);
            *out = q;
        }
    }
    SxError error = t->error;
    if (stats) {
        stats->allocations = t->attempt;
        stats->peak_bytes = t->peak;
        stats->reason = t->reason;
    }
    while (t->head)
        release(t->head + 1);
    active = NULL;
    owned_bytes -= sizeof(Tx);
    free(t);
    return error;
}
SxError sx_rat_set(SxRat *q, const char *n, const char *d, const SxLimits *l, SxStats *s) {
    return run(q, NULL, NULL, 's', NULL, NULL, n, d, NULL, l, s);
}
SxError sx_rat_op(SxRat *q, char op, const SxRat *a, const SxRat *b, const SxLimits *l,
                  SxStats *s) {
    if (!q)
        return early(s, SX_INVALID, SX_AR_BAD_ARGUMENT);
    if (op != '+' && op != '-' && op != '*' && op != '/')
        return early(s, SX_INVALID, SX_AR_BAD_ARGUMENT);
    return run(q, NULL, NULL, op, a, b, NULL, NULL, NULL, l, s);
}
SxError sx_rat_cmp(int *out, const SxRat *a, const SxRat *b, const SxLimits *l, SxStats *s) {
    if (!out)
        return early(s, SX_INVALID, SX_AR_BAD_ARGUMENT);
    return run(NULL, out, NULL, 'c', a, b, NULL, NULL, NULL, l, s);
}
SxError sx_rat_string(char **out, const SxRat *a, const SxLimits *l, SxStats *s) {
    if (!out)
        return early(s, SX_INVALID, SX_AR_BAD_ARGUMENT);
    return run(NULL, NULL, out, 'e', a, NULL, NULL, NULL, NULL, l, s);
}

SxError sx_rat_import(SxRat *out, mpz_srcptr z, const SxLimits *l, SxStats *s) {
    if (!out || !z || z->_mp_alloc < 0 || z->_mp_size == INT_MIN)
        return early(s, SX_INVALID, SX_AR_BAD_ARGUMENT);
    size_t n = length(z), max = l && l->max_limbs ? l->max_limbs : 1048576;
    if (max < 4 || max > (size_t)INT_MAX / 64)
        return early(s, SX_INVALID, SX_AR_BAD_ARGUMENT);
    if (n > max || n > (size_t)INT_MAX / 64)
        return early(s, SX_LIMIT, SX_AR_LIMBS);
    if ((z->_mp_alloc > 0 && (n > (size_t)z->_mp_alloc || !z->_mp_d)) ||
        (n && (!z->_mp_d || !z->_mp_d[n - 1])))
        return early(s, SX_INVALID, SX_AR_BAD_ARGUMENT);
    return run(out, NULL, NULL, 'i', NULL, NULL, NULL, NULL, z, l, s);
}

static int integer(const SxRat *q) {
    return valid(q) && q->den._mp_size == 1 && q->den._mp_d[0] == 1;
}
SxError sx_integer_gcd(SxRat *out, const SxRat *a, const SxRat *b, const SxLimits *l, SxStats *s) {
    if (!out || !integer(a) || !integer(b))
        return early(s, SX_INTERNAL, SX_AR_BAD_ARGUMENT);
    return run(out, NULL, NULL, 'g', a, b, NULL, NULL, NULL, l, s);
}
SxError sx_integer_divexact(SxRat *out, const SxRat *a, const SxRat *b, const SxLimits *l,
                            SxStats *s) {
    if (!out || !integer(a) || !integer(b) || b->num._mp_size <= 0)
        return early(s, SX_INTERNAL, SX_AR_BAD_ARGUMENT);
    return run(out, NULL, NULL, 'x', a, b, NULL, NULL, NULL, l, s);
}
