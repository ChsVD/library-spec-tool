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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_violation_retry.simplex_find_violation_retry_lib */
/*@ Extern Coq
 (simplex_find_violation_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_prefix : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_slots_memory : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_scan_slots_except : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (simplex_scan_unused_memory : Z -> Z -> Assertion)
 (simplex_scan_output_separation : Z -> Z -> Z -> Prop)
 (In : {A} -> A -> list A -> Prop)
*/

int sx_find_violation(struct SxState *s, int *row, int *direction)
/*@ separated_search
 With (BAS : list Z) (HL : list Z) (HU : list Z) (VN : list Z) (VD : list Z) (LN : list Z) (LD : list Z) (UN : list Z) (UD : list Z) M V S P Q
 Require s == S && row == P && direction == Q &&
 simplex_scan_output_separation(s, row, direction) &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= Znth(j, BAS, 0) && Znth(j, BAS, 0) < V)) &&
 (forall j, (In(j, BAS) && (Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) =>
    (-2147483648 <= Znth(j, VN, 0) && Znth(j, VN, 0) <= 2147483647 && 1 <= Znth(j, VD, 0) && Znth(j, VD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HL, 0) != 0) =>
    (-2147483648 <= Znth(j, LN, 0) && Znth(j, LN, 0) <= 2147483647 && 1 <= Znth(j, LD, 0) && Znth(j, LD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HU, 0) != 0) =>
    (-2147483648 <= Znth(j, UN, 0) && Znth(j, UN, 0) <= 2147483647 && 1 <= Znth(j, UD, 0) && Znth(j, UD, 0) <= 2147483647)) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, BAS) * simplex_scan_slots_memory(s, BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(s, M) * undef_data_at(row) * undef_data_at(direction)
 Ensure exists R D, simplex_find_violation_spec(BAS, HL, HU, VN, VD, LN, LD, UN, UD, V, M, __return, R, D) &&
 store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->vars), V) *
 IntArray::full(((struct SxState *)S)->basic, M, BAS) * simplex_scan_slots_memory(((struct SxState *)S), BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(((struct SxState *)S), M) * data_at(((int *)P), int, R) * data_at(((int *)Q), int, D)
*/
/*@ separated_search */
{
    int i, b, cmp, d, best = s->vars;
    *row = -1; *direction = 0;
    /* The completed row prefix determines the current stable minimum. */
    /*@ Inv Assert exists R D,
 s == S && row == P && direction == Q &&
 0 <= i && i <= M && 0 <= best && best <= V &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= Znth(j, BAS, 0) && Znth(j, BAS, 0) < V)) &&
 (forall j, (In(j, BAS) && (Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) =>
    (-2147483648 <= Znth(j, VN, 0) && Znth(j, VN, 0) <= 2147483647 && 1 <= Znth(j, VD, 0) && Znth(j, VD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HL, 0) != 0) =>
    (-2147483648 <= Znth(j, LN, 0) && Znth(j, LN, 0) <= 2147483647 && 1 <= Znth(j, LD, 0) && Znth(j, LD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HU, 0) != 0) =>
    (-2147483648 <= Znth(j, UN, 0) && Znth(j, UN, 0) <= 2147483647 && 1 <= Znth(j, UD, 0) && Znth(j, UD, 0) <= 2147483647)) &&
 simplex_scan_prefix(BAS, HL, HU, VN, VD, LN, LD, UN, UD, V, i, best, R, D) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, BAS) * simplex_scan_slots_memory(s, BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(s, M) * store(row, R) * store(direction, D) *
 undef_data_at(&b) * undef_data_at(&cmp) * undef_data_at(&d)
 */
    for (i = 0; i < s->rows; i++) {
        b = s->basic[i]; d = 0;
        /* Expose the current basic slot and frame every other slot; restore at loop cut. */
        /*@ Assert exists R D,
 s == S && row == P && direction == Q &&
 0 <= i && i < M && 0 <= b && b < V && b == Znth(i, BAS, 0) && In(b, BAS) &&
 0 <= best && best <= V && 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= Znth(j, BAS, 0) && Znth(j, BAS, 0) < V)) &&
 (forall j, (In(j, BAS) && (Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) =>
    (-2147483648 <= Znth(j, VN, 0) && Znth(j, VN, 0) <= 2147483647 && 1 <= Znth(j, VD, 0) && Znth(j, VD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HL, 0) != 0) =>
    (-2147483648 <= Znth(j, LN, 0) && Znth(j, LN, 0) <= 2147483647 && 1 <= Znth(j, LD, 0) && Znth(j, LD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HU, 0) != 0) =>
    (-2147483648 <= Znth(j, UN, 0) && Znth(j, UN, 0) <= 2147483647 && 1 <= Znth(j, UD, 0) && Znth(j, UD, 0) <= 2147483647)) &&
 simplex_scan_prefix(BAS, HL, HU, VN, VD, LN, LD, UN, UD, V, i, best, R, D) &&
 store(&(s->rows), M) * store(&(s->vars), V) * IntArray::full(s->basic, M, BAS) *
 simplex_scan_slots_except(s, BAS, HL, HU, VN, VD, LN, LD, UN, UD, b) *
 store(&(s->has_lower[b]), Znth(b, HL, 0)) * store(&(s->has_upper[b]), Znth(b, HU, 0)) *
 (((Znth(b, HL, 0) != 0 || Znth(b, HU, 0) != 0) && store(&(s->value[b].num), Znth(b, VN, 0)) * store(&(s->value[b].den), Znth(b, VD, 0))) ||
       ((!(Znth(b, HL, 0) != 0 || Znth(b, HU, 0) != 0)) && undef_data_at(&(s->value[b].num)) * undef_data_at(&(s->value[b].den)))) *
 (((Znth(b, HL, 0) != 0) && store(&(s->lower[b].num), Znth(b, LN, 0)) * store(&(s->lower[b].den), Znth(b, LD, 0))) ||
       ((!(Znth(b, HL, 0) != 0)) && undef_data_at(&(s->lower[b].num)) * undef_data_at(&(s->lower[b].den)))) *
 (((Znth(b, HU, 0) != 0) && store(&(s->upper[b].num), Znth(b, UN, 0)) * store(&(s->upper[b].den), Znth(b, UD, 0))) ||
       ((!(Znth(b, HU, 0) != 0)) && undef_data_at(&(s->upper[b].num)) * undef_data_at(&(s->upper[b].den)))) *
 simplex_scan_unused_memory(s, M) * store(row, R) * store(direction, D) *
 store(&d, 0) * undef_data_at(&cmp)
        */
        if (s->has_lower[b]) {
            if (!rat_compare(&s->value[b], &s->lower[b], &cmp)
                /*@ where (out_undef) A = Znth(b, VN, 0), B = Znth(b, VD, 0), C = Znth(b, LN, 0), D = Znth(b, LD, 0) */) return 0;
            if (cmp < 0) d = 1;
        }
        if (s->has_upper[b]) {
            if (!rat_compare(&s->value[b], &s->upper[b], &cmp)
                /*@ where (out_undef) A = Znth(b, VN, 0), B = Znth(b, VD, 0), C = Znth(b, UN, 0), D = Znth(b, UD, 0) */) return 0;
            if (cmp > 0) d = -1;
        }
        if (d != 0 && b < best) {
            best = b; *row = i; *direction = d;
        }
    }
    return 1;
}
