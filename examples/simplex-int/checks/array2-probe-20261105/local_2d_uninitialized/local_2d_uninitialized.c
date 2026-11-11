#include "array2_ext_def.h"
int probe(void)
/*@ Require emp Ensure __return == 7 && emp */
{ int a[2][3]; a[1][2] = 7; return a[1][2]; }
