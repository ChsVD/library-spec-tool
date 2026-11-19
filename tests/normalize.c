/* Exact expected rows exercise signed/zero remainders and wide common factors. */
#include "../src/solver.c"
#include <assert.h>
#include <stdio.h>
int mpz_cmp(mpz_srcptr, mpz_srcptr);
static void check(mpz_srcptr got, long expected) {
    mpz_t z; mpz_init(z); mpz_set_si(z, expected);
    assert(mpz_cmp(got,z)==0); mpz_clear(z);
}
static void small_case(long d,long c,long a,long b,long ed,long ec,long ea,long eb) {
    struct InequList input={integers(3),NULL};
    struct table t=build(&input,2);
    mpz_set_si(t.d,d);mpz_set_si(t.c,c);mpz_set_si(t.a,a);mpz_set_si(t.a+1,b);
    normalize(&t,0);
    check(t.d,ed);check(t.c,ec);check(t.a,ea);check(t.a+1,eb);check(t.a+2,0);
    destroy(&t);release(input.coef,3);
}
int main(void) {
    small_case(168,-84,126,42,4,-2,3,1);
    small_case(105,-30,-14,15,105,-30,-14,15);
    small_case(60,24,0,0,5,2,0,0);
    small_case(1,-7,9,0,1,-7,9,0);
    struct InequList input={integers(3),NULL};
    struct table t=build(&input,2);
    mpz_t factor,two,tmp,mult;mpz_init(factor);mpz_init(two);mpz_init(tmp);mpz_init(mult);
    mpz_set_ui(factor,1);mpz_set_ui(two,2);
    for(int i=0;i<160;++i){mpz_mul(tmp,factor,two);mpz_set(factor,tmp);}
    mpz_set_ui(mult,1);mpz_set_ui(two,1);mpz_addmul(tmp,mult,two);mpz_set(factor,tmp);
    mpz_ptr destinations[4]={t.d,t.c,t.a,t.a+1};long scales[4]={12,-18,30,42};
    for(int i=0;i<4;++i){mpz_set_si(mult,scales[i]);mpz_mul(tmp,factor,mult);mpz_set(destinations[i],tmp);}
    normalize(&t,0);check(t.d,2);check(t.c,-3);check(t.a,5);check(t.a+1,7);check(t.a+2,0);
    destroy(&t);release(input.coef,3);mpz_clear(factor);mpz_clear(two);mpz_clear(tmp);mpz_clear(mult);
    struct InequList constant={integers(1),NULL};t=build(&constant,0);
    mpz_set_ui(t.d,15);mpz_set_si(t.c,-30);normalize(&t,0);check(t.d,1);check(t.c,-2);
    destroy(&t);release(constant.coef,1);
    puts("6 normalization fixtures passed");return 0;
}
