#include "array2_ext_def.h"
int probe(int a[][3])
/*@ With (M : list (list Z))
Require IntArray2::full(a, 2, 3, M)
Ensure exists N, __return == 7 && IntArray2::full(a, 2, 3, N) */
{ a[1][2] = 7; return a[1][2]; }
