/* Experimental limits, not mathematical restrictions of Simplex. */
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
;

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_entering_preserve.simplex_find_entering_preserve_lib */
/*@ Extern Coq
 (Forall : {A} -> (A -> Prop) -> list A -> Prop)
 (Z::le : Z -> Z -> Prop)
 (Z::ge : Z -> Z -> Prop)
 (Zrange : Z -> Z -> list Z)
 (simplex_find_entering_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_enter_skipped : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
 (simplex_scan_read_memory : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_scan_read_except : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_enter_num_memory : Z -> Z -> Z -> list Z -> Assertion)
 (simplex_enter_num_except : Z -> Z -> Z -> list Z -> Z -> Assertion)
*/
int sx_find_entering(struct SxState *s, int row, int direction, int *entering)
/*@ framed_search
    With V S R D O (IB CN HL HU VN VD LN LD UN UD : list Z)
    Require s == S && row == R && direction == D && entering == O && 0 <= V && V <= 24 && (V == 0 || (0 <= row && row < 16)) &&
      -2147483648 <= row && row <= 2147483647 &&
      -2147483648 <= direction && direction <= 2147483647 &&
      Zlength(CN) == V && Zlength(VN) == V && Zlength(VD) == V &&
      Forall(Z::le(-2147483647), CN) && Forall(Z::ge(2147483647), CN) &&
      Forall(Z::le(-2147483647), VN) && Forall(Z::ge(2147483647), VN) &&
      Forall(Z::le(1), VD) && Forall(Z::ge(2147483647), VD) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HL, 0) != 0) =>
        (-2147483647 <= Znth(i, LN, 0) && Znth(i, LN, 0) <= 2147483647 &&
         1 <= Znth(i, LD, 0) && Znth(i, LD, 0) <= 2147483647)) &&
      (forall (i: Z), (0 <= i && i < V && Znth(i, HU, 0) != 0) =>
        (-2147483647 <= Znth(i, UN, 0) && Znth(i, UN, 0) <= 2147483647 &&
         1 <= Znth(i, UD, 0) && Znth(i, UD, 0) <= 2147483647)) &&
      store(&(s->vars), V) * IntArray::full(s->is_basic, V, IB) *
      simplex_scan_read_memory(s, Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD) *
      simplex_enter_num_memory(s, row, V, CN) * undef_data_at(entering)
    Ensure exists e, simplex_find_entering_spec(IB, CN, HL, HU, VN, VD, LN, LD, UN, UD,
        D, V, __return, e) && store(&(((struct SxState *)S)->vars), V) *
      IntArray::full(((struct SxState *)S)->is_basic, V, IB) *
      simplex_scan_read_memory(((struct SxState *)S), Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD) *
      simplex_enter_num_memory(((struct SxState *)S), R, V, CN) * data_at(((int *)O), int, e)
*/
{
    int j, increase, cmp;
    *entering = -1;
    /* Every processed column is an exact skip; no choice or failure occurred. */
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
      store(&(s->vars), V) * IntArray::full(s->is_basic, V, IB) *
      simplex_scan_read_memory(s, Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD) *
      simplex_enter_num_memory(s, row, V, CN) * data_at(entering, int, -1) * undef_data_at(&increase) * undef_data_at(&cmp)
    */
    for (j = 0; j < s->vars; j++) {
        /* Expose only the current read cells and retain all other owned cells. */
        /*@ Assert
      s == S && row == R && direction == D && entering == O &&
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
      store(&(s->vars), V) * IntArray::missing_i(s->is_basic, j, 0, V, IB) * store(&(s->is_basic[j]), Znth(j, IB, 0)) *
      simplex_scan_read_except(s, Zrange(0, V), HL, HU, VN, VD, LN, LD, UN, UD, j) *
      simplex_enter_num_except(s, row, V, CN, j) * store(&(s->a[row][j].num), Znth(j, CN, 0)) *
      store(&(s->has_lower[j]), Znth(j, HL, 0)) * store(&(s->has_upper[j]), Znth(j, HU, 0)) *
      (((Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0) && store(&(s->value[j].num), Znth(j, VN, 0)) * store(&(s->value[j].den), Znth(j, VD, 0))) ||
       ((!(Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) && emp)) *
      ((Znth(j, HL, 0) != 0 && store(&(s->lower[j].num), Znth(j, LN, 0)) * store(&(s->lower[j].den), Znth(j, LD, 0))) ||
       (Znth(j, HL, 0) == 0 && emp)) *
      ((Znth(j, HU, 0) != 0 && store(&(s->upper[j].num), Znth(j, UN, 0)) * store(&(s->upper[j].den), Znth(j, UD, 0))) ||
       (Znth(j, HU, 0) == 0 && emp)) *
      data_at(entering, int, -1) * undef_data_at(&increase) * undef_data_at(&cmp)
        */
        if (!s->is_basic[j] && s->a[row][j].num != 0) {
            increase = (s->a[row][j].num > 0 && direction > 0) ||
                       (s->a[row][j].num < 0 && direction < 0);
            if (increase) {
                if (!s->has_upper[j]) { *entering = j; return 1; }
                if (!rat_compare(&s->value[j], &s->upper[j], &cmp)) return 0;
                if (cmp < 0) { *entering = j; return 1; }
            } else {
                if (!s->has_lower[j]) { *entering = j; return 1; }
                if (!rat_compare(&s->value[j], &s->lower[j], &cmp)) return 0;
                if (cmp > 0) { *entering = j; return 1; }
            }
        }
    }
    return 1;
}
