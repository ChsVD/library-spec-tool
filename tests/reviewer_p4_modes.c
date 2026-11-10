/* Check the public list API on interleaved removed rows/columns and
 * differently scaled inputs. Inputs and results have disjoint lifetimes. */
#include "sx_solver_contract.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(x) do { if (!(x)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x); exit(2); } } while (0)
struct InequList { mpz_ptr coef; struct InequList *next; };

static void sample(unsigned mask) {
    enum { ROWS=5, VARS=7, WIDTH=VARS+1, COUNT=ROWS*WIDTH };
    int matrix[ROWS][WIDTH]={{-7},{0},{0},{0},{0}};
    matrix[1][0]=15; matrix[1][2]=-15; matrix[1][6]=-15;
    matrix[3][2]=7; matrix[4][6]=11;
    __mpz_struct flat[COUNT]; unsigned int words[COUNT];
    struct InequList list[ROWS];
    for (size_t i=0;i<ROWS;i++) {
        for (size_t j=0;j<WIDTH;j++) {
            size_t k=i*WIDTH+j; int v=matrix[i][j];
            words[k]=(unsigned int)(v<0?-v:v);
            flat[k]=(__mpz_struct){0,(v>0)-(v<0),&words[k]};
        }
        list[i]=(struct InequList){&flat[i*WIDTH],i+1<ROWS?&list[i+1]:NULL};
    }
    SxSolverLimits l={0}; l.disable_optimizations=mask;
    SxResult b; sx_result_init(&b);
    sx_check_qcp(list,VARS,&l,&b);
    CHECK(b.error==SX_OK && b.rational_status==SX_Q_UNSAT && b.integer_status==SX_Z_UNSAT);
    CHECK(b.conflict.bound_source_row!=0 && b.conflict.bound_source_row!=2);
    CHECK(b.conflict.basic_variable==VARS+b.conflict.bound_source_row);
    CHECK(b.conflict.blocker_count==2 && b.conflict.row!=0 && b.conflict.row!=2);
    size_t attempts=b.stats.allocations, peak=b.stats.peak_bytes;
    sx_result_clear(&b);
    l.max_table_bytes=peak-1;
    sx_check_qcp(list,VARS,&l,&b);
    CHECK(b.error==SX_OK && b.rational_status==SX_Q_UNKNOWN && b.reason==SX_REASON_SPACE);
    CHECK(!b.conflict.present && !b.witness); sx_result_clear(&b);
    l.max_table_bytes=peak; sx_check_qcp(list,VARS,&l,&b);
    CHECK(b.error==SX_OK && b.rational_status==SX_Q_UNSAT); sx_result_clear(&b);
    l.max_table_bytes=0; l.fail_at=attempts;
    sx_check_qcp(list,VARS,&l,&b);
    CHECK(b.error==SX_OOM && b.rational_status==SX_Q_NOT_RUN && b.integer_status==SX_Z_NOT_DECIDED && !b.conflict.present && !b.witness);
    sx_result_clear(&b); l.fail_at=0;
    /* Make the final row redundant, so the same compressed system is feasible. */
    flat[4*WIDTH+6]._mp_size=0;
    sx_check_qcp(list,VARS,&l,&b);
    CHECK(b.error==SX_OK && b.rational_status==SX_Q_FEASIBLE && b.witness_length==VARS && b.stats.verified_rows==ROWS);
    for (size_t i=0;i<ROWS;i++) CHECK(list[i].coef==&flat[i*WIDTH] && list[i].next==(i+1<ROWS?&list[i+1]:NULL));
    sx_result_clear(&b);
    /* Earlier positive constant row must not hide an invalid last object. */
    flat[0]._mp_size=1;
    flat[COUNT-1]._mp_alloc=-1;
    sx_check_qcp(list,VARS,&l,&b);
    CHECK(b.error==SX_INVALID && !b.conflict.present);
    CHECK(b.rational_status==SX_Q_NOT_RUN);
    sx_result_clear(&b);
    unsigned int limbs[5]={0,0,0,0,1};
    flat[COUNT-1]=(__mpz_struct){0,5,limbs}; l.arithmetic.max_limbs=4;
    sx_check_qcp(list,VARS,&l,&b);
    CHECK(b.error==SX_OK && b.rational_status==SX_Q_UNKNOWN && b.reason==SX_REASON_LIMBS && !b.conflict.present);
    sx_result_clear(&b);
    CHECK(sx_runtime_live_bytes()==0);
}

int main(void) {
    for (unsigned mask=0; mask<16; mask++) sample(mask);
    puts("Public QCP list entry, source indices, model length, retained input and late malformed object passed in 16 modes.");
    return 0;
}
