/* Independently proved additive framed_search interface. Original separated_search case retained.
 * Run simplex_find_violation_preserve-20261103113604; controller final-check passed/done/errors=[].
 * Minimal read slice is returned unchanged. Other state is preserved by a caller frame;
 * no unconditional whole-S readonly claim when outputs alias unread state.
 */
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


/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_find_violation_preserve.simplex_find_violation_preserve_lib */
/*@ Extern Coq
 (simplex_find_violation_spec : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_prefix : list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (simplex_scan_read_memory : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Assertion)
 (simplex_scan_read_except : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Assertion)
 (In : {A} -> A -> list A -> Prop)
*/

int sx_find_violation(struct SxState *s, int *row, int *direction)
/*@ framed_search
 With (BAS : list Z) (HL : list Z) (HU : list Z) (VN : list Z) (VD : list Z) (LN : list Z) (LD : list Z) (UN : list Z) (UD : list Z) M V S P Q
 Require s == S && row == P && direction == Q &&
 0 <= M && M <= 16 && 0 <= V && V <= 24 &&
 (forall j, (0 <= j && j < M) => (0 <= Znth(j, BAS, 0) && Znth(j, BAS, 0) < V)) &&
 (forall j, (In(j, BAS) && (Znth(j, HL, 0) != 0 || Znth(j, HU, 0) != 0)) =>
    (-2147483648 <= Znth(j, VN, 0) && Znth(j, VN, 0) <= 2147483647 && 1 <= Znth(j, VD, 0) && Znth(j, VD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HL, 0) != 0) =>
    (-2147483648 <= Znth(j, LN, 0) && Znth(j, LN, 0) <= 2147483647 && 1 <= Znth(j, LD, 0) && Znth(j, LD, 0) <= 2147483647)) &&
 (forall j, (In(j, BAS) && Znth(j, HU, 0) != 0) =>
    (-2147483648 <= Znth(j, UN, 0) && Znth(j, UN, 0) <= 2147483647 && 1 <= Znth(j, UD, 0) && Znth(j, UD, 0) <= 2147483647)) &&
 store(&(s->rows), M) * store(&(s->vars), V) *
 IntArray::full(s->basic, M, BAS) * simplex_scan_read_memory(s, BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 undef_data_at(row) * undef_data_at(direction)
 Ensure exists R D, simplex_find_violation_spec(BAS, HL, HU, VN, VD, LN, LD, UN, UD, V, M, __return, R, D) &&
 store(&(((struct SxState *)S)->rows), M) * store(&(((struct SxState *)S)->vars), V) *
 IntArray::full(((struct SxState *)S)->basic, M, BAS) * simplex_scan_read_memory(((struct SxState *)S), BAS, HL, HU, VN, VD, LN, LD, UN, UD) *
 data_at(((int *)P), int, R) * data_at(((int *)Q), int, D)
*/
;
