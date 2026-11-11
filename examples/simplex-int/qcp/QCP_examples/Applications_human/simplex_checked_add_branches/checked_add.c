#include "limits.h"

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib */
/*@ Extern Coq (checked_add_flag : Z -> Z -> Z) */

static int checked_add(int x, int y, int *out)
  /*@ out_undef
      With A B
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              undef_data_at(out)
      Ensure __return == checked_add_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A + B)) ||
              (__return == 0 && undef_data_at(out)))
  */
  /*@ out_known
      With A B old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              data_at(out, int, old)
      Ensure __return == checked_add_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A + B)) ||
              (__return == 0 && data_at(out, int, old)))
  */
  /*@ out_undef */
  /*@ out_known */
{
    if (x == INT_MIN || y == INT_MIN) return 0;
    if (y > 0 && x > INT_MAX - y) return 0;
    if (y < 0 && x < -INT_MAX - y) return 0;
    *out = x + y;
    return 1;
}
