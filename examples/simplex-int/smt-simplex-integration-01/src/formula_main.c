#include "smt_solver.h"
extern FILE *yyin;
extern int yyparse(void);
extern SmtProp *root;
int main(int argc, char **argv) {
    if (argc != 2 || !(yyin = fopen(argv[1],"r"))) return 2;
    if (yyparse() || !root) return 3;
    fclose(yyin);
    int result = smt_solver(root);
    printf("RESULT %d\n",result);
    return 0;
}
