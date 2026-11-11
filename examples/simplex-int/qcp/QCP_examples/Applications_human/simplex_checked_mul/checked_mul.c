#include "limits.h"

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib */
/*@ Extern Coq (checked_mul_flag : Z -> Z -> Z) */

static int checked_mul(int x, int y, int *out)
  /*@ With A B known old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              ((known == 0 && undef_data_at(out)) ||
               (known == 1 && data_at(out, int, old)))
      Ensure __return == checked_mul_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A * B)) ||
              (__return == 0 &&
               ((known == 0 && undef_data_at(out)) ||
                (known == 1 && data_at(out, int, old)))))
  */
{
    int ax = x, ay = y;
    if (x == INT_MIN || y == INT_MIN) return 0;
    if (ax < 0) ax = -ax;
    if (ay < 0) ay = -ay;
    if (ay != 0 && ax > INT_MAX / ay) return 0;
    *out = x * y;
    return 1;
}
