/* Test-only access to the actual pivot; no checker enters production. */
#include "../src/solver.c"
#include <assert.h>
#include <stdio.h>
int mpz_cmp(mpz_srcptr, mpz_srcptr);

/* Columns are constant, x, y: each stable variable's original affine form. */
static const long form[5][3] = {
    {0, 1, 0}, {0, 0, 1}, {3, 2, -3}, {-2, -4, 5}, {7, 6, 1}
};

static void check(const struct table *t)
{
    mpz_t lhs, rhs, value;
    mpz_init(lhs);
    mpz_init(rhs);
    mpz_init(value);
    for (size_t r = 0; r < t->rows; ++r) {
        assert(t->d[r]._mp_size > 0);
        assert(t->row[t->basic[r]] == r);
        for (size_t v = 0; v < t->cols; ++v)
            if (t->row[v] != SIZE_MAX)
                assert(t->a[r * t->cols + v]._mp_size == 0);
        for (size_t coordinate = 0; coordinate < 3; ++coordinate) {
            mpz_set_si(value, form[t->basic[r]][coordinate]);
            mpz_mul(lhs, t->d + r, value);
            if (coordinate == 0)
                mpz_set(rhs, t->c + r);
            else
                mpz_set_ui(rhs, 0);
            for (size_t v = 0; v < t->cols; ++v) {
                mpz_set_si(value, form[v][coordinate]);
                mpz_addmul(rhs, t->a + r * t->cols + v, value);
            }
            assert(mpz_cmp(lhs, rhs) == 0);
        }
    }
    for (size_t v = 0; v < t->cols; ++v)
        if (t->row[v] != SIZE_MAX)
            assert(t->basic[t->row[v]] == v);
    mpz_clear(lhs);
    mpz_clear(rhs);
    mpz_clear(value);
}

int main(void)
{
    struct InequList nodes[3];
    for (size_t r = 0; r < 3; ++r) {
        nodes[r].coef = integers(3);
        nodes[r].next = r + 1 < 3 ? nodes + r + 1 : NULL;
        for (size_t c = 0; c < 3; ++c)
            mpz_set_si(nodes[r].coef + c, form[r + 2][c]);
    }
    struct table t = build(nodes, 2);
    check(&t);
    unsigned positive = 0, negative = 0, auxiliary = 0;
    /* Exercise reversible changes of basis, including auxiliary columns. */
    for (size_t step = 0; step < 90; ++step) {
        size_t r = step % t.rows;
        size_t e = (step / t.rows) % t.cols;
        for (size_t offset = 0; offset < t.cols; ++offset) {
            size_t v = (e + offset) % t.cols;
            int sign = t.a[r * t.cols + v]._mp_size;
            if (t.row[v] == SIZE_MAX && sign != 0) {
                positive += sign > 0;
                negative += sign < 0;
                auxiliary += v >= 2;
                pivot(&t, r, v);
                check(&t);
                break;
            }
        }
    }
    assert(positive && negative && auxiliary);
    destroy(&t);
    for (size_t r = 0; r < 3; ++r)
        release(nodes[r].coef, 3);
    printf("pivot identities passed: positive=%u negative=%u auxiliary=%u\n",
           positive, negative, auxiliary);
    return 0;
}
