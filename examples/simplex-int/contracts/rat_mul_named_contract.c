/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_mul.simplex_rat_mul_lib */
/*@ Extern Coq
      (simplex_rat_mul_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_mul_result : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int rat_mul(const struct SxRat *x, const struct SxRat *y,
                   struct SxRat *out)
  /*@ out_undef
      With A B C D
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              undef_data_at(&(out->num)) * undef_data_at(&(out->den))
      Ensure __return == simplex_rat_mul_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 && exists P Q,
                simplex_rat_mul_result(A, B, C, D, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * C * Q == P * (B * D) &&
                (A * C != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && undef_data_at(&(out->num)) * undef_data_at(&(out->den))))
  */
  /*@ out_known
      With A B C D oldn oldd
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              store(&(out->num), oldn) * store(&(out->den), oldd)
      Ensure __return == simplex_rat_mul_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 && exists P Q,
                simplex_rat_mul_result(A, B, C, D, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * C * Q == P * (B * D) &&
                (A * C != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(out->num), oldn) * store(&(out->den), oldd)))
  */
;
