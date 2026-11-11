#include "array2_ext_def.h"
int probe(int a[][3])
/*@ Require IntArray2::undef_full(a, 2, 3)
Ensure exists N, __return == 7 && IntArray2::mixed_full(a, 2, 3, N) */
{ a[1][2] = 7; return a[1][2]; }
