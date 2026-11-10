/* Independent public-API probe for reviewer_p3.py. One instance per process. */
#include "sx_solver_contract.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(x) do { if (!(x)) { fprintf(stderr,"line %d: %s\n", __LINE__, #x); exit(2); } } while (0)

static void print_value(const SxRat *q) {
    char *s = NULL;
    CHECK(sx_rat_string(&s, q, NULL, NULL) == SX_OK);
    printf(" %s", s);
    sx_string_free(s);
}
struct InequList { mpz_ptr coef; struct InequList *next; };

int main(int argc, char **argv) {
    size_t m, n, pivots, bytes, limbs;
    CHECK(scanf("%zu %zu %zu %zu %zu", &m, &n, &pivots, &bytes, &limbs) == 5);
    CHECK(m <= 50 && n <= 25);
    size_t count = m*(n+1);
    __mpz_struct *coefficients = calloc(count+1, sizeof(*coefficients));
    SxRat *owners = calloc(count+1, sizeof(*owners));
    char (*original)[256] = calloc(count+1, sizeof(*original));
    CHECK(coefficients && owners && original);
    for (size_t i = 0; i < count; ++i) {
        CHECK(scanf("%255s", original[i]) == 1);
        sx_rat_init(&owners[i]);
        CHECK(sx_rat_set(&owners[i], original[i], "1", NULL, NULL) == SX_OK);
        coefficients[i] = owners[i].num; /* Readable borrowed object, limbs owned by owners. */
    }
    SxSolverLimits limits = {0};
    limits.max_pivots = pivots;
    limits.max_table_bytes = bytes;
    limits.arithmetic.max_limbs = limbs;
    SxResult r;
    sx_result_init(&r);
    CHECK(argc==1);
    (void)argv;
    struct InequList *nodes=calloc(m+1,sizeof(*nodes));
    CHECK(nodes);
    for (size_t i=0; i<m; ++i) {
        nodes[i].coef=&coefficients[i*(n+1)];
        nodes[i].next=i+1<m ? &nodes[i+1] : NULL;
    }
    sx_check_qcp(m?nodes:NULL,n,&limits,&r);
    for (size_t i=0; i<m; ++i) {
        CHECK(nodes[i].coef==&coefficients[i*(n+1)]);
        CHECK(nodes[i].next==(i+1<m ? &nodes[i+1] : NULL));
    }
    free(nodes);
    for (size_t i = 0; i < count; ++i) {
        CHECK(coefficients[i]._mp_size == owners[i].num._mp_size && coefficients[i]._mp_alloc == owners[i].num._mp_alloc && coefficients[i]._mp_d == owners[i].num._mp_d);
        char *s=NULL;
        CHECK(sx_rat_string(&s, &owners[i], NULL, NULL) == SX_OK);
        CHECK(!strncmp(s, original[i], strlen(original[i])) && !strcmp(s+strlen(original[i]), "/1"));
        sx_string_free(s);
        sx_rat_clear(&owners[i]);
    }
    free(original); free(owners); free(coefficients);
    printf("%d %d %d %d %zu %zu %zu\n", (int)r.error,(int)r.rational_status,(int)r.integer_status,(int)r.reason,r.stats.pivots,r.stats.peak_bytes,r.witness_length);
    if (r.rational_status != SX_Q_FEASIBLE) CHECK(!r.witness && !r.witness_length);
    if (r.rational_status == SX_Q_FEASIBLE) CHECK(r.stats.verified_rows == m);
    for (size_t i=0; i<r.witness_length; ++i) {
        char *s=NULL;
        CHECK(sx_rat_string(&s,&r.witness[i],NULL,NULL)==SX_OK);
        printf("%s\n",s); sx_string_free(s);
    }
    CHECK((r.rational_status == SX_Q_UNSAT) == (r.conflict.present != 0));
    if (r.conflict.present) {
        const SxConflict *cf = &r.conflict;
        printf("conflict %zu %zu %d %zu",cf->basic_variable,cf->bound_source_row,cf->to_lower,cf->blocker_count);
        print_value(&cf->constant); print_value(&cf->required); print_value(&cf->attainable); putchar('\n');
        for (size_t i=0; i<cf->blocker_count; ++i) {
            const SxBlocker *b=&cf->blockers[i];
            printf("blocker %zu %zu %d",b->variable,b->source_row,b->is_lower);
            print_value(&b->coefficient); print_value(&b->bound); putchar('\n');
        }
    }
    sx_result_clear(&r);
    sx_result_clear(&r);
    CHECK(sx_live_blocks() == 0);
    return 0;
}
