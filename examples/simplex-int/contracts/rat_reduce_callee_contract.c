/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_positive_gcd.simplex_positive_gcd_lib */
/*@ Extern Coq (Zgcd : Z -> Z -> Z) */

static int positive_gcd(int a, int b)
  /*@ With A B
      Require a == A && b == B &&
              0 <= a && a <= 2147483647 &&
              0 <= b && b <= 2147483647 && emp
      Ensure __return == Zgcd(A, B) && emp
  */
;
