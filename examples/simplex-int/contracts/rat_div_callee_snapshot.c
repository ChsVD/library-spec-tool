/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib */
/*@ Extern Coq (checked_mul_flag : Z -> Z -> Z) */

static int checked_mul(int x, int y, int *out)
  /*@ out_undef
      With A B
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              undef_data_at(out)
      Ensure __return == checked_mul_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A * B)) ||
              (__return == 0 && undef_data_at(out)))
  */
  /*@ out_known
      With A B old
      Require x == A && y == B &&
              -2147483648 <= x && x <= 2147483647 &&
              -2147483648 <= y && y <= 2147483647 &&
              data_at(out, int, old)
      Ensure __return == checked_mul_flag(A, B) &&
             ((__return == 1 && data_at(out, int, A * B)) ||
              (__return == 0 && data_at(out, int, old)))
  */
;

struct SxRat { int num; int den; };
/*@ Extern Coq (Zgcd : Z -> Z -> Z) */
/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib */
/*@ Extern Coq
      (Zabs : Z -> Z)
      (simplex_rat_reduce_result : Z -> Z -> Z -> Z -> Prop)
*/

static void rat_reduce(struct SxRat *r)
  /*@ With N D
      Require -2147483647 <= N && N <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(r->num), N) * store(&(r->den), D)
      Ensure exists P Q,
              simplex_rat_reduce_result(N, D, P, Q) &&
              -2147483647 <= P && P <= 2147483647 &&
              1 <= Q && Q <= 2147483647 &&
              Zgcd(Zabs(P), Q) == 1 && N * Q == P * D &&
              (N != 0 || (P == 0 && Q == 1)) &&
              (Zgcd(Zabs(N), D) != 1 || (P == N && Q == D)) &&
              store(&(r->num), P) * store(&(r->den), Q)
  */
;
