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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_add.simplex_rat_add_lib */
/*@ Extern Coq
      (simplex_rat_add_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_add_result : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int rat_add(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out)
  /*@ r_eq_x
      With A B C E
      Require out == x &&
              -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E)
      Ensure __return == simplex_rat_add_flag(A, B, C, E) &&
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_add_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && (A * E + C * B) * Q == P * (B * E) &&
                (A * E + C * B != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(x->num), A) * store(&(x->den), B)))
  */
  /*@ out_undef
      With A B C E
      Require -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E) *
              undef_data_at(&(out->num)) * undef_data_at(&(out->den))
      Ensure __return == simplex_rat_add_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_add_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && (A * E + C * B) * Q == P * (B * E) &&
                (A * E + C * B != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && undef_data_at(&(out->num)) * undef_data_at(&(out->den))))
  */
  /*@ out_known
      With A B C E oldn oldd
      Require -2147483647 <= A && A <= 2147483647 &&
              -2147483647 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= E && E <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), E) *
              store(&(out->num), oldn) * store(&(out->den), oldd)
      Ensure __return == simplex_rat_add_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_add_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && (A * E + C * B) * Q == P * (B * E) &&
                (A * E + C * B != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(out->num), oldn) * store(&(out->den), oldd)))
  */
/*@ r_eq_x */
/*@ out_undef */
/*@ out_known */
{
    int p, q, n, d;
    if (!checked_mul(x->num, y->den, &p)
      /*@ where (out_undef) A = A_r_eq_x, B = E_r_eq_x $ r_eq_x
          where (out_undef) A = A_out_undef, B = E_out_undef $ out_undef
          where (out_undef) A = A_out_known, B = E_out_known $ out_known */) return 0;
    if (!checked_mul(y->num, x->den, &q)
      /*@ where (out_undef) A = C_r_eq_x, B = B_r_eq_x $ r_eq_x
          where (out_undef) A = C_out_undef, B = B_out_undef $ out_undef
          where (out_undef) A = C_out_known, B = B_out_known $ out_known */) return 0;
    if (!checked_add(p, q, &n)
      /*@ where (out_undef) A = A_r_eq_x * E_r_eq_x, B = C_r_eq_x * B_r_eq_x $ r_eq_x
          where (out_undef) A = A_out_undef * E_out_undef, B = C_out_undef * B_out_undef $ out_undef
          where (out_undef) A = A_out_known * E_out_known, B = C_out_known * B_out_known $ out_known */) return 0;
    if (!checked_mul(x->den, y->den, &d)
      /*@ where (out_undef) A = B_r_eq_x, B = E_r_eq_x $ r_eq_x
          where (out_undef) A = B_out_undef, B = E_out_undef $ out_undef
          where (out_undef) A = B_out_known, B = E_out_known $ out_known */) return 0;
    out->num = n; out->den = d;
    rat_reduce(out);
    return 1;
}
