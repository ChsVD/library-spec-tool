/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib */
/*@ Extern Coq
      (simplex_rat_compare_flag : Z -> Z -> Z -> Z -> Z)
      (simplex_rat_compare_order : Z -> Z -> Z -> Z -> Z)
*/

static int rat_compare(const struct SxRat *x, const struct SxRat *y,
                       int *order)
  /*@ out_undef
      With A B C D
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              undef_data_at(order)
      Ensure __return == simplex_rat_compare_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 &&
                data_at(order, int, simplex_rat_compare_order(A, B, C, D))) ||
              (__return == 0 && undef_data_at(order)))
  */
  /*@ out_known
      With A B C D old
      Require -2147483648 <= A && A <= 2147483647 &&
              -2147483648 <= C && C <= 2147483647 &&
              1 <= B && B <= 2147483647 &&
              1 <= D && D <= 2147483647 &&
              store(&(x->num), A) * store(&(x->den), B) *
              store(&(y->num), C) * store(&(y->den), D) *
              data_at(order, int, old)
      Ensure __return == simplex_rat_compare_flag(A, B, C, D) &&
             store(&(x->num), A) * store(&(x->den), B) *
             store(&(y->num), C) * store(&(y->den), D) *
             ((__return == 1 &&
                data_at(order, int, simplex_rat_compare_order(A, B, C, D))) ||
              (__return == 0 && data_at(order, int, old)))
  */
;
