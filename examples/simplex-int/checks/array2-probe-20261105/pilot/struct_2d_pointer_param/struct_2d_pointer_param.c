#include "array2_ext_def.h"
struct Matrix { int a[2][3]; };
int probe(struct Matrix *p)
/*@ Require undef_data_at(&(p->a[1][2])) Ensure __return == 7 && data_at(&(p->a[1][2]), int, 7) */
{ p->a[1][2] = 7; return p->a[1][2]; }
