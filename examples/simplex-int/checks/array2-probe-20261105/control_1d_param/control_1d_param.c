#include "array2_ext_def.h"
int probe(int a[])
/*@ With (M : list Z) Require IntArray::full(a, 6, M)
Ensure exists N, __return == 7 && IntArray::full(a, 6, N) */
{ a[5] = 7; return a[5]; }
