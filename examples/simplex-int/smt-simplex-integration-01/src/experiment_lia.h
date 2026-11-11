#include "lia_theory.h"
#ifdef FME_ONLY
#define experiment_lia lia_theory_deduction
#else
int experiment_lia(InequList*, InequList*, int*, int, int, int, int, int);
#endif
