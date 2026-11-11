#include "array2_ext_def.h"
struct Matrix { int a[2][3]; };
int probe(struct Matrix *p)
/*@ With (M : list (list Z)) Require IntArray2::full(p->a, 2, 3, M)
Ensure exists N, __return == 7 && IntArray2::full(p->a, 2, 3, N) */
{ p->a[1][2] = 7; return p->a[1][2]; }
