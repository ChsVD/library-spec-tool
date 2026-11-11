#include <limits.h>
#include "simplex.h"
int probe_int_max = INT_MAX;
int probe_int_min = INT_MIN;
int probe_int_bytes = __SIZEOF_INT__;
int probe_char_bits = __CHAR_BIT__;
int probe_pointer_bytes = __SIZEOF_POINTER__;
int probe_input_cap = SX_INPUT_VARS;
int probe_rows_cap = SX_ROWS;
int probe_vars_cap = SX_VARS;
