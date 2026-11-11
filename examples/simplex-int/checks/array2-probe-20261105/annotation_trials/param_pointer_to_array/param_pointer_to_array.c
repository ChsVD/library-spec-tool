#include "array2_ext_def.h"
int probe(int (*a)[3])
/*@ Require undef_data_at(*(a + 1) + 2) Ensure __return == 7 && data_at(*(a + 1) + 2, int, 7) */
{ a[1][2] = 7; return a[1][2]; }
