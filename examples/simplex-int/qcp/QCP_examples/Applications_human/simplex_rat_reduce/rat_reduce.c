/* Callee declaration/contract copied from contracts/simplex_function_contracts.c. */
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

struct SxRat { int num; int den; };

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
{
    int n = r->num;
    int g;
    if (n < 0) n = -n;
    g = positive_gcd(n, r->den);
    r->num /= g;
    r->den /= g;
}
