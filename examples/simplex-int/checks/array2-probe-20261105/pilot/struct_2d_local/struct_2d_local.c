#include "array2_ext_def.h"
struct Matrix { int a[2][3]; };
int probe(void)
/*@ Require emp Ensure __return == 7 && emp */
{ struct Matrix s; s.a[1][2] = 7; return s.a[1][2]; }
