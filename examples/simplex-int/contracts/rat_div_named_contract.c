/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_div.simplex_rat_div_lib */
/*@ Extern Coq
      (simplex_rat_div_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_div_result : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

static int rat_div(const struct SxRat *x, const struct SxRat *y,
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
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
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
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
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
      Ensure __return == simplex_rat_div_flag(A, B, C, E) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), E) *
             ((__return == 1 && exists P Q,
                simplex_rat_div_result(A, B, C, E, P, Q) &&
                -2147483647 <= P && P <= 2147483647 &&
                1 <= Q && Q <= 2147483647 &&
                Zgcd(Zabs(P), Q) == 1 && A * E * Q == P * (B * C) &&
                (A != 0 || (P == 0 && Q == 1)) &&
                store(&(out->num), P) * store(&(out->den), Q)) ||
              (__return == 0 && store(&(out->num), oldn) * store(&(out->den), oldd)))
  */
;
