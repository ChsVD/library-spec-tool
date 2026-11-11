#include "array2_ext_def.h"
int probe(int a[])
/*@ Require undef_data_at(a + 5) Ensure __return == 7 && data_at(a + 5, int, 7) */
{ a[5] = 7; return a[5]; }
