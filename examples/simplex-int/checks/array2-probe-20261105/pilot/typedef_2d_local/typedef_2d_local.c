#include "array2_ext_def.h"
typedef int Matrix[2][3];
int probe(void)
/*@ Require emp Ensure __return == 7 && emp */
{ Matrix a; a[1][2] = 7; return a[1][2]; }
