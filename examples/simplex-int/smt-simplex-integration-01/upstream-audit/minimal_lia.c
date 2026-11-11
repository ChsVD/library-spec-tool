#include "lia_theory.h"
int main(void) {
  InequList *eq=initInequList(), *tail=initInequList();
  InequList *lo=initInequList(), *hi=initInequList();
  hi->coef=calloc(2,sizeof(int)); hi->coef[0]=-1; hi->coef[1]=2; hi->strict=-1; hi->next=lo;
  lo->coef=calloc(2,sizeof(int)); lo->coef[0]=1; lo->coef[1]=-2; lo->strict=-1; lo->next=tail;
  int value[2]={0,1};
  printf("RESULT=%d (expected 0 over integers)\n",lia_theory_deduction(eq,hi,value,1,-1,-1,-1,-1));
  free_InequList(eq); return 0;
}
