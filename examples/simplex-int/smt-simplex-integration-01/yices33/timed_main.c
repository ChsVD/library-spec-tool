#define _POSIX_C_SOURCE 200809L
#include "smt_solver.h"
#include <time.h>
extern FILE *yyin;
extern int yyparse(void);
extern SmtProp *root;
static double ms(void){
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC,&t);
    return t.tv_sec*1000.0+t.tv_nsec/1e6;
}
int main(int argc,char **argv){
    double start=ms();
    if(argc!=2 || !(yyin=fopen(argv[1],"r"))) return 2;
    if(yyparse() || !root)return 3;
    fclose(yyin);
    double solve=ms();
    int result=smt_solver(root);
    double end=ms();
    fprintf(stderr,"RESULT %d total_ms=%.6f solve_ms=%.6f\n",result,end-start,end-solve);
    return 0;
}
