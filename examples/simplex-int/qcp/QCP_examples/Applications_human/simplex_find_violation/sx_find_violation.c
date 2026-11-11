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

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_violation.simplex_find_violation_lib */
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
/*@ out_undef
 With (B : list Z) (HL : list Z) (HU : list Z) (VN : list Z) (VD : list Z) (LN : list Z) (LD : list Z) (UN : list Z) (UD : list Z) M V
 Require simplex_scan_output_separation(s, row, direction) &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= B[j] && B[j] < V)) &&
 (forall j, In(j, B) =>
   (((HL[j] != 0 || HU[j] != 0) => (-2147483648 <= VN[j] && VN[j] <= 2147483647 && 1 <= VD[j] && VD[j] <= 2147483647)) &&
    (HL[j] != 0 => (-2147483648 <= LN[j] && LN[j] <= 2147483647 && 1 <= LD[j] && LD[j] <= 2147483647)) &&
    (HU[j] != 0 => (-2147483648 <= UN[j] && UN[j] <= 2147483647 && 1 <= UD[j] && UD[j] <= 2147483647)))) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, B) *
 simplex_scan_slots_memory(s, B, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(s, M) * undef_data_at(row) * undef_data_at(direction)
 Ensure exists R D, simplex_find_violation_spec(B, HL, HU, VN, VD, LN, LD, UN, UD, V, M, __return, R, D) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, B) *
 simplex_scan_slots_memory(s, B, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(s, M) * store(row, R) * store(direction, D)
*/
/*@ out_known
 With (B : list Z) (HL : list Z) (HU : list Z) (VN : list Z) (VD : list Z) (LN : list Z) (LD : list Z) (UN : list Z) (UD : list Z) M V oldrow olddirection
 Require simplex_scan_output_separation(s, row, direction) &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= B[j] && B[j] < V)) &&
 (forall j, In(j, B) =>
   (((HL[j] != 0 || HU[j] != 0) => (-2147483648 <= VN[j] && VN[j] <= 2147483647 && 1 <= VD[j] && VD[j] <= 2147483647)) &&
    (HL[j] != 0 => (-2147483648 <= LN[j] && LN[j] <= 2147483647 && 1 <= LD[j] && LD[j] <= 2147483647)) &&
    (HU[j] != 0 => (-2147483648 <= UN[j] && UN[j] <= 2147483647 && 1 <= UD[j] && UD[j] <= 2147483647)))) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, B) *
 simplex_scan_slots_memory(s, B, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(s, M) * store(row, oldrow) * store(direction, olddirection)
 Ensure exists R D, simplex_find_violation_spec(B, HL, HU, VN, VD, LN, LD, UN, UD, V, M, __return, R, D) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, B) *
 simplex_scan_slots_memory(s, B, HL, HU, VN, VD, LN, LD, UN, UD) *
 simplex_scan_unused_memory(s, M) * store(row, R) * store(direction, D)
*/
/*@ out_undef */
/*@ out_known */
{
    int i, b, cmp, d, best = s->vars;
    *row = -1; *direction = 0;
    /*@ Inv
 out_undef: Assert exists R D,
 s == s@pre && row == row@pre && direction == direction@pre &&
 0 <= i && i <= M_out_undef && 0 <= best && best <= V_out_undef &&
 0 <= M_out_undef && M_out_undef <= 16 && 0 <= V_out_undef && V_out_undef <= 24 &&
 (forall j, (0 <= j && j < M_out_undef) => (0 <= B_out_undef[j] && B_out_undef[j] < V_out_undef)) &&
 (forall j, In(j, B_out_undef) =>
   (((HL_out_undef[j] != 0 || HU_out_undef[j] != 0) => (-2147483648 <= VN_out_undef[j] && VN_out_undef[j] <= 2147483647 && 1 <= VD_out_undef[j] && VD_out_undef[j] <= 2147483647)) &&
    (HL_out_undef[j] != 0 => (-2147483648 <= LN_out_undef[j] && LN_out_undef[j] <= 2147483647 && 1 <= LD_out_undef[j] && LD_out_undef[j] <= 2147483647)) &&
    (HU_out_undef[j] != 0 => (-2147483648 <= UN_out_undef[j] && UN_out_undef[j] <= 2147483647 && 1 <= UD_out_undef[j] && UD_out_undef[j] <= 2147483647)))) &&
 simplex_scan_prefix(B_out_undef, HL_out_undef, HU_out_undef, VN_out_undef, VD_out_undef, LN_out_undef, LD_out_undef, UN_out_undef, UD_out_undef, V_out_undef, i, best, R, D) &&
 store(&(s->rows), M_out_undef) * store(&(s->vars), V_out_undef) *
 IntArray::full(s->basic, M_out_undef, B_out_undef) *
 simplex_scan_slots_memory(s, B_out_undef, HL_out_undef, HU_out_undef, VN_out_undef, VD_out_undef, LN_out_undef, LD_out_undef, UN_out_undef, UD_out_undef) *
 simplex_scan_unused_memory(s, M_out_undef) * store(row, R) * store(direction, D) *
 undef_data_at(&b) * undef_data_at(&cmp) * undef_data_at(&d);
 out_known: Assert exists R D,
 s == s@pre && row == row@pre && direction == direction@pre &&
 0 <= i && i <= M_out_known && 0 <= best && best <= V_out_known &&
 0 <= M_out_known && M_out_known <= 16 && 0 <= V_out_known && V_out_known <= 24 &&
 (forall j, (0 <= j && j < M_out_known) => (0 <= B_out_known[j] && B_out_known[j] < V_out_known)) &&
 (forall j, In(j, B_out_known) =>
   (((HL_out_known[j] != 0 || HU_out_known[j] != 0) => (-2147483648 <= VN_out_known[j] && VN_out_known[j] <= 2147483647 && 1 <= VD_out_known[j] && VD_out_known[j] <= 2147483647)) &&
    (HL_out_known[j] != 0 => (-2147483648 <= LN_out_known[j] && LN_out_known[j] <= 2147483647 && 1 <= LD_out_known[j] && LD_out_known[j] <= 2147483647)) &&
    (HU_out_known[j] != 0 => (-2147483648 <= UN_out_known[j] && UN_out_known[j] <= 2147483647 && 1 <= UD_out_known[j] && UD_out_known[j] <= 2147483647)))) &&
 simplex_scan_prefix(B_out_known, HL_out_known, HU_out_known, VN_out_known, VD_out_known, LN_out_known, LD_out_known, UN_out_known, UD_out_known, V_out_known, i, best, R, D) &&
 store(&(s->rows), M_out_known) * store(&(s->vars), V_out_known) *
 IntArray::full(s->basic, M_out_known, B_out_known) *
 simplex_scan_slots_memory(s, B_out_known, HL_out_known, HU_out_known, VN_out_known, VD_out_known, LN_out_known, LD_out_known, UN_out_known, UD_out_known) *
 simplex_scan_unused_memory(s, M_out_known) * store(row, R) * store(direction, D) *
 undef_data_at(&b) * undef_data_at(&cmp) * undef_data_at(&d)
 */
    for (i = 0; i < s->rows; i++) {
        b = s->basic[i]; d = 0;
        
        if (s->has_lower[b]) {
            if (!rat_compare(&s->value[b], &s->lower[b], &cmp)
                /*@ where (out_undef) A = VN_out_undef[b], B = VD_out_undef[b], C = LN_out_undef[b], D = LD_out_undef[b] $ out_undef
                    where (out_undef) A = VN_out_known[b], B = VD_out_known[b], C = LN_out_known[b], D = LD_out_known[b] $ out_known */) return 0;
            if (cmp < 0) d = 1;
        }
        if (s->has_upper[b]) {
            if (!rat_compare(&s->value[b], &s->upper[b], &cmp)
                /*@ where (out_undef) A = VN_out_undef[b], B = VD_out_undef[b], C = UN_out_undef[b], D = UD_out_undef[b] $ out_undef
                    where (out_undef) A = VN_out_known[b], B = VD_out_known[b], C = UN_out_known[b], D = UD_out_known[b] $ out_known */) return 0;
            if (cmp > 0) d = -1;
        }
        if (d != 0 && b < best) {
            best = b; *row = i; *direction = d;
        }
    }
    return 1;
}
