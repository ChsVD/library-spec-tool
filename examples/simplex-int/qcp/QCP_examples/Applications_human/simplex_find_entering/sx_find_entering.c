#define SX_INPUT_VARS 8
#define SX_ROWS 16
#define SX_VARS (SX_INPUT_VARS + SX_ROWS)
#define SX_UNKNOWN (-1)
#define SX_FEASIBLE 0
#define SX_UNSAT 1

struct SxRat { int num; int den; };

/* Same null-terminated representation as QCP's fme.c (no sentinel node). */
struct InequList { int *coef; struct InequList *next; };

/* row i: basic[i] = rhs[i] + sum_j a[i][j] * value[j].
 * All basic-variable columns are zero. Nonbasic values satisfy their bounds.
 * Successful arithmetic produces reduced fractions with positive denominators.
 */
struct SxState {
    int rows, vars, inputs;
    int basic[SX_ROWS];
    int is_basic[SX_VARS];
    int has_lower[SX_VARS], has_upper[SX_VARS];
    struct SxRat lower[SX_VARS], upper[SX_VARS], value[SX_VARS];
    struct SxRat rhs[SX_ROWS], a[SX_ROWS][SX_VARS];
};


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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_entering.simplex_find_entering_lib */
/*@ Extern Coq
 (Forall : {A} -> (A -> Prop) -> list A -> Prop)
 (Z::le : Z -> Z -> Prop)
 (Z::ge : Z -> Z -> Prop)
 (simplex_find_entering_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_enter_skipped : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
 (simplex_enter_slots_memory : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_enter_slots_except : Z -> Z -> Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_enter_coeff_except : Z -> Z -> Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_enter_unused_memory : Z -> Assertion)
 (simplex_enter_output_separation : Z -> Z -> Prop)
*/
int sx_find_entering(struct SxState *s, int row, int direction, int *entering)
/*@ separated_search
    With V S R D O (IB CN CD HL HU VN VD LN LD UN UD : list Z)
    Require s == S && row == R && direction == D && entering == O && 0 <= V && V <= 24 && (V == 0 || (0 <= row && row < 16)) &&
      -2147483648 <= row && row <= 2147483647 &&
      -2147483648 <= direction && direction <= 2147483647 &&
      Zlength(CN) == V && Zlength(CD) == V && Zlength(VN) == V && Zlength(VD) == V &&
      Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) &&
      Forall(Z::le(1), CD) && Forall(Z::ge(2147483647), CD) &&
      Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) &&
      Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HL, 0) != 0) =>
        (-2147483647 <= Znth(i, LN, 0) && Znth(i, LN, 0) <= 2147483647 &&
         1 <= Znth(i, LD, 0) && Znth(i, LD, 0) <= 2147483647)) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HU, 0) != 0) =>
        (-2147483647 <= Znth(i, UN, 0) && Znth(i, UN, 0) <= 2147483647 &&
         1 <= Znth(i, UD, 0) && Znth(i, UD, 0) <= 2147483647)) && simplex_enter_output_separation(s, entering) &&
      store(&(s->vars), V) *
      IntArray::full(s->is_basic, V, IB) * IntArray::undef_seg(s->is_basic, V, 24) *
      IntArray::full(s->has_lower, V, HL) * IntArray::undef_seg(s->has_lower, V, 24) *
      IntArray::full(s->has_upper, V, HU) * IntArray::undef_seg(s->has_upper, V, 24) *
      simplex_enter_slots_memory(s, row, V, CN, CD, HL, HU, VN, VD, LN, LD, UN, UD) * simplex_enter_unused_memory(s) * undef_data_at(entering)
    Ensure exists e, simplex_find_entering_spec(IB, CN, HL, HU, VN, VD, LN, LD, UN, UD,
        D, V, __return, e) && store(&(((struct SxState *)S)->vars), V) *
      IntArray::full(((struct SxState *)S)->is_basic, V, IB) * IntArray::undef_seg(((struct SxState *)S)->is_basic, V, 24) *
      IntArray::full(((struct SxState *)S)->has_lower, V, HL) * IntArray::undef_seg(((struct SxState *)S)->has_lower, V, 24) *
      IntArray::full(((struct SxState *)S)->has_upper, V, HU) * IntArray::undef_seg(((struct SxState *)S)->has_upper, V, 24) *
      simplex_enter_slots_memory(((struct SxState *)S), R, V, CN, CD, HL, HU, VN, VD, LN, LD, UN, UD) * simplex_enter_unused_memory(((struct SxState *)S)) * data_at(((int *)O), int, e)
*/
/*@ separated_search */
{
    int j, increase, cmp;
    *entering = -1;
    /* Processed columns are all exact skips; neither choice nor failure has occurred. */
    /*@ Inv Assert
      s == S && row == R && direction == D && entering == O &&
      0 <= j && j <= V && 0 <= V && V <= 24 && (V == 0 || (0 <= row && row < 16)) &&
      Zlength(VN) == V && Zlength(VD) == V &&
      Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) &&
      Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HL, 0) != 0) =>
        (-2147483647 <= Znth(i, LN, 0) && Znth(i, LN, 0) <= 2147483647 &&
         1 <= Znth(i, LD, 0) && Znth(i, LD, 0) <= 2147483647)) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HU, 0) != 0) =>
        (-2147483647 <= Znth(i, UN, 0) && Znth(i, UN, 0) <= 2147483647 &&
         1 <= Znth(i, UD, 0) && Znth(i, UD, 0) <= 2147483647)) &&
      simplex_enter_skipped(IB, CN, HL, HU, VN, VD, LN, LD, UN, UD, direction, j) &&
      store(&(s->vars), V) *
      IntArray::full(s->is_basic, V, IB) * IntArray::undef_seg(s->is_basic, V, 24) *
      IntArray::full(s->has_lower, V, HL) * IntArray::undef_seg(s->has_lower, V, 24) *
      IntArray::full(s->has_upper, V, HU) * IntArray::undef_seg(s->has_upper, V, 24) *
      simplex_enter_slots_memory(s, row, V, CN, CD, HL, HU, VN, VD, LN, LD, UN, UD) * simplex_enter_unused_memory(s) * data_at(entering, int, -1) * undef_data_at(&increase) * undef_data_at(&cmp)
    */
    for (j = 0; j < s->vars; j++) {
        /*@ Assert s == S && row == R && direction == D && entering == O &&
      0 <= j && j < V && 0 < V && V <= 24 && 0 <= row && row < 16 &&
      Zlength(VN) == V && Zlength(VD) == V &&
      Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) &&
      Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HL, 0) != 0) =>
        (-2147483647 <= Znth(i, LN, 0) && Znth(i, LN, 0) <= 2147483647 &&
         1 <= Znth(i, LD, 0) && Znth(i, LD, 0) <= 2147483647)) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HU, 0) != 0) =>
        (-2147483647 <= Znth(i, UN, 0) && Znth(i, UN, 0) <= 2147483647 &&
         1 <= Znth(i, UD, 0) && Znth(i, UD, 0) <= 2147483647)) &&
      simplex_enter_skipped(IB, CN, HL, HU, VN, VD, LN, LD, UN, UD, direction, j) &&
      store(&(s->vars), V) *
      IntArray::full(s->is_basic, V, IB) * IntArray::undef_seg(s->is_basic, V, 24) *
      IntArray::full(s->has_lower, V, HL) * IntArray::undef_seg(s->has_lower, V, 24) *
      IntArray::full(s->has_upper, V, HU) * IntArray::undef_seg(s->has_upper, V, 24) *
      simplex_enter_slots_except(s, row, V, CN, CD, HL, HU, VN, VD, LN, LD, UN, UD, j) *
      store(&(s->a[row][j].num), Znth(j, CN, 0)) * store(&(s->a[row][j].den), Znth(j, CD, 0)) *
      simplex_enter_coeff_except(s, row, V, CN, CD, j) *
      store(&(s->value[j].num), Znth(j, VN, 0)) * store(&(s->value[j].den), Znth(j, VD, 0)) *
      ((Znth(j, HL, 0) == 0 && undef_data_at(&(s->lower[j].num)) * undef_data_at(&(s->lower[j].den))) ||
       (Znth(j, HL, 0) != 0 && store(&(s->lower[j].num), Znth(j, LN, 0)) * store(&(s->lower[j].den), Znth(j, LD, 0)))) *
      ((Znth(j, HU, 0) == 0 && undef_data_at(&(s->upper[j].num)) * undef_data_at(&(s->upper[j].den))) ||
       (Znth(j, HU, 0) != 0 && store(&(s->upper[j].num), Znth(j, UN, 0)) * store(&(s->upper[j].den), Znth(j, UD, 0)))) * simplex_enter_unused_memory(s) * data_at(entering, int, -1) * undef_data_at(&increase) * undef_data_at(&cmp)
        */
        if (!s->is_basic[j] && s->a[row][j].num != 0) {
            increase = (s->a[row][j].num > 0 && direction > 0) ||
                       (s->a[row][j].num < 0 && direction < 0);
            if (increase) {
                if (!s->has_upper[j]) { *entering = j; return 1; }
                if (!rat_compare(&s->value[j], &s->upper[j], &cmp)
                  /*@ where (out_undef) A = Znth(j, VN, 0), B = Znth(j, VD, 0), C = Znth(j, UN, 0), D = Znth(j, UD, 0) */) return 0;
                if (cmp < 0) { *entering = j; return 1; }
            } else {
                if (!s->has_lower[j]) { *entering = j; return 1; }
                if (!rat_compare(&s->value[j], &s->lower[j], &cmp)
                  /*@ where (out_undef) A = Znth(j, VN, 0), B = Znth(j, VD, 0), C = Znth(j, LN, 0), D = Znth(j, LD, 0) */) return 0;
                if (cmp > 0) { *entering = j; return 1; }
            }
        }
    }
    return 1;
}
