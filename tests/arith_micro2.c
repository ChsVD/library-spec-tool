#define _POSIX_C_SOURCE 200809L
#include "backend.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
int mpz_cmp(mpz_srcptr, mpz_srcptr);
void mpz_tdiv_r(mpz_ptr, mpz_srcptr, mpz_srcptr);
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static int unit(mpz_srcptr a) { return (a->_mp_size==1 || a->_mp_size==-1) && a->_mp_d[0]==1; }
static int equal_abs(mpz_srcptr a, mpz_srcptr b) {
    int na=abs(a->_mp_size),nb=abs(b->_mp_size);if(na!=nb)return 0;
    for(int i=0;i<na;++i) { if(a->_mp_d[i]!=b->_mp_d[i])return 0; }
    return 1;
}
static void read_hex(mpz_ptr z) {
    char text[32768];assert(scanf("%32767s",text)==1);
    size_t k=text[0]=='-'?1:0;int negative=k!=0;assert(text[k]=='0' && text[k+1]=='x');k+=2;
    mpz_t base,digit,tmp,one;mpz_init(base);mpz_init(digit);mpz_init(tmp);mpz_init(one);mpz_set_ui(base,16);mpz_set_ui(one,1);mpz_set_ui(z,0);
    for(;text[k];++k){unsigned v=text[k]>='0'&&text[k]<='9'?(unsigned)(text[k]-'0'):(unsigned)(text[k]-'a'+10);assert(v<16);mpz_mul(tmp,z,base);mpz_set_ui(digit,v);mpz_addmul(tmp,digit,one);mpz_set(z,tmp);}
    if(negative){mpz_neg(tmp,z);mpz_set(z,tmp);}mpz_clear(base);mpz_clear(digit);mpz_clear(tmp);mpz_clear(one);
}
/* Test-only algebraic candidates; no production backend is modified. */
static void evaluate(int operation,int mode,mpz_ptr out,mpz_srcptr a,mpz_srcptr b,mpz_ptr scratch) {
    if(operation==0){
        if(mode==0)mpz_gcd(out,a,b);
        else {assert(a->_mp_size>0);mpz_tdiv_r(scratch,b,a);if(scratch->_mp_size==0)mpz_abs(out,a);else mpz_gcd(out,a,scratch);}
    }else{
        if(mode && unit(b)){if(b->_mp_size>0)mpz_set(out,a);else mpz_neg(out,a);}
        else if(mode && equal_abs(a,b))mpz_set_si(out,(a->_mp_size<0)==(b->_mp_size<0)?1:-1);
        else mpz_divexact(out,a,b);
    }
}
int main(void) {
    int count;assert(scanf("%d",&count)==1);
    for(int i=0;i<count;++i){
        int id,operation;assert(scanf("%d %d",&id,&operation)==2);
        mpz_t a,b,expected,out[2],scratch[2],copy_a,copy_b;mpz_init(a);mpz_init(b);mpz_init(expected);mpz_init(copy_a);mpz_init(copy_b);
        for(int mode=0;mode<2;++mode){mpz_init(out[mode]);mpz_init(scratch[mode]);}
        read_hex(a);read_hex(b);read_hex(expected);mpz_set(copy_a,a);mpz_set(copy_b,b);
        for(int mode=0;mode<2;++mode){evaluate(operation,mode,out[mode],a,b,scratch[mode]);assert(mpz_cmp(out[mode],expected)==0);}
        unsigned long loops=1;double elapsed;
        do {double start=now();for(unsigned long k=0;k<loops;++k)evaluate(operation,0,out[0],a,b,scratch[0]);elapsed=now()-start;if(elapsed<0.003 && loops<1048576)loops*=2;else break;}while(1);
        for(int rep=0;rep<5;++rep)for(int slot=0;slot<2;++slot){int mode=(slot+rep)%2;double start=now();for(unsigned long k=0;k<loops;++k)evaluate(operation,mode,out[mode],a,b,scratch[mode]);double seconds=now()-start;assert(mpz_cmp(out[mode],expected)==0);printf("%d %d %d %lu %.12f\n",id,mode,rep,loops,seconds);}
        assert(mpz_cmp(a,copy_a)==0 && mpz_cmp(b,copy_b)==0);
        mpz_clear(a);mpz_clear(b);mpz_clear(expected);mpz_clear(copy_a);mpz_clear(copy_b);for(int mode=0;mode<2;++mode){mpz_clear(out[mode]);mpz_clear(scratch[mode]);}
    }return 0;
}
