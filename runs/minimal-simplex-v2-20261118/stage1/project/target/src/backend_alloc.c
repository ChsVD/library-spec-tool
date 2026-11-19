#include "gmp/minigmp/gmp_def.h"
#include <stdlib.h>
#include <string.h>

/* External allocation services: successful allocation is a precondition. */
unsigned int *gmp_alloc_limbs(int n) {
    return malloc((size_t)n * sizeof(unsigned int));
}
void gmp_free_limbs(unsigned int *p, int n) {
    (void)n;
    free(p);
}
unsigned int *gmp_realloc_limbs(unsigned int *p, int old, int n) {
    unsigned int *q = gmp_alloc_limbs(n);
    memcpy(q, p, (size_t)(old < n ? old : n) * sizeof(*q));
    free(p);
    return q;
}
mpz_ptr malloc_mpz_struct(void) {
    return malloc(sizeof(__mpz_struct));
}
void free_mpz_struct(mpz_ptr p) { free(p); }
struct gmp_div_inverse *malloc_gmp_div_inverse(void) {
    return malloc(sizeof(struct gmp_div_inverse));
}
void free_gmp_div_inverse(struct gmp_div_inverse *p) { free(p); }
void int_swap(int *a, int *b) {
    int t = *a; *a = *b; *b = t;
}
void mp_ptr_swap(unsigned int **a, unsigned int **b) {
    unsigned int *t = *a; *a = *b; *b = t;
}
void mpz_srcptr_swap(mpz_srcptr *a, mpz_srcptr *b) {
    mpz_srcptr t = *a; *a = *b; *b = t;
}
int mpn_zero_p(unsigned int *p, int n) {
    for (int i = 0; i < n; i++)
        if (p[i]) return 0;
    return 1;
}