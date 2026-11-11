#include "limits.h"

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib */
/*@ Extern Coq (checked_add_flag : Z -> Z -> Z) */

static int checked_add(int x, int y, int *out)
  /*@ With A B known old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              ((known == 0 && undef_data_at(out)) ||
               (known == 1 && data_at(out, int, old)))
      Ensure __return == checked_add_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A + B)) ||
              (__return == 0 &&
               ((known == 0 && undef_data_at(out)) ||
                (known == 1 && data_at(out, int, old)))))
  */
{
    if (x == INT_MIN || y == INT_MIN) return 0;
    if (y > 0 && x > INT_MAX - y) return 0;
    if (y < 0 && x < -INT_MAX - y) return 0;
    *out = x + y;
    return 1;
}
