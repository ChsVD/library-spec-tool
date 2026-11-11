#include "array2_ext_def.h"
int probe(void)
/*@ Require emp Ensure __return == 7 && emp */
{ int a[6]; a[5] = 7; return a[5]; }
