/* Test-only replacement for profile.o: serialize exact canonical table states. */
#include "profile.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
static FILE *trace;
static void write_bytes(const void *p,size_t size,size_t count) { assert(fwrite(p,size,count,trace)==count); }
static void integer(mpz_srcptr z) {
    int n=z->_mp_size<0 ? -z->_mp_size : z->_mp_size;
    write_bytes(&z->_mp_size,sizeof(z->_mp_size),1);
    if(n)write_bytes(z->_mp_d,sizeof(*z->_mp_d),(size_t)n);
}
void sx_profile_reset(void) { trace=fopen(getenv("SX_EXACT_TRACE"),"wb");assert(trace); }
void sx_profile_begin(void) {}
void sx_profile_normalize_begin(void) {}
void sx_profile_normalize_end(int value) { (void)value; }
void sx_profile_finish(int answer) { write_bytes(&answer,sizeof(answer),1);assert(fclose(trace)==0);trace=NULL; }
void sx_profile_table(size_t rows,size_t cols,mpz_srcptr d,mpz_srcptr c,mpz_srcptr a,const size_t *row,int initial) {
    write_bytes(&initial,sizeof(initial),1);write_bytes(&rows,sizeof(rows),1);write_bytes(&cols,sizeof(cols),1);write_bytes(row,sizeof(*row),cols);
    for(size_t i=0;i<rows;++i){integer(d+i);integer(c+i);for(size_t j=0;j<cols;++j)integer(a+i*cols+j);}
}
void mpz_tdiv_r(mpz_ptr,mpz_srcptr,mpz_srcptr);
#define FORWARD(name) void sx_profile_##name(mpz_ptr out,mpz_srcptr a,mpz_srcptr b){mpz_##name(out,a,b);}
FORWARD(gcd)
FORWARD(mul)
FORWARD(divexact)
FORWARD(addmul)
FORWARD(tdiv_r)
