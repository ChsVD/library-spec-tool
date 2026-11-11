#define _POSIX_C_SOURCE 200809L
#include <time.h>
#include "experiment_lia.h"
#include "../simplex/simplex.h"
static long long ns(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec*1000000000LL+t.tv_nsec;}
extern int __real_sx_check(struct SxState*,int,int,const int [SX_ROWS][SX_INPUT_VARS+1],int);
int __wrap_sx_check(struct SxState*s,int m,int n,const int a[SX_ROWS][SX_INPUT_VARS+1],int lim){
 long long t=ns();int rc=__real_sx_check(s,m,n,a,lim);long long dt=ns()-t;
 fprintf(stderr,"KERNEL sx %d %d %d %lld\n",m,n,rc,dt);return rc;
}
extern int __real_lia_theory_deduction(InequList*,InequList*,int*,int,int,int,int,int);
int __wrap_lia_theory_deduction(InequList*e,InequList*i,int*u,int n,int a,int b,int c,int d){
 long long t=ns();int rc=__real_lia_theory_deduction(e,i,u,n,a,b,c,d);long long dt=ns()-t;
 fprintf(stderr,"KERNEL lia %d %d %lld\n",n,rc,dt);return rc;
}
