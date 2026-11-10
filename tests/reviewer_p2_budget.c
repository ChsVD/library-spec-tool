/* Verify the peak reported for an operation is an enforceable budget. */
#include "sx_table.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define REQUIRE(x) do { if (!(x)) { fprintf(stderr, "line %d: %s\n", __LINE__, #x); exit(1); } } while (0)

struct InequList { mpz_ptr coef; struct InequList *next; };

static void equals(const SxRat *value, const char *expected) {
    char *text = NULL;
    REQUIRE(value && sx_rat_string(&text, value, NULL, NULL) == SX_OK);
    REQUIRE(strcmp(text, expected) == 0);
    sx_string_free(text);
}

static void budget_probe(const SxProblem *p) {
    SxTable *t = NULL;
    SxTableStats created, switched, measured;
    SxTableLimits cap = {0};
    REQUIRE(sx_table_create(&t, p, NULL, &created) == SX_OK);
    REQUIRE(created.peak_table_bytes >= sx_table_bytes(t));
    REQUIRE(sx_table_pivot(&t, 0, 0, 0, NULL, &switched) == SX_OK);
    sx_table_destroy(t);
    t = NULL;
    cap.max_table_bytes = created.peak_table_bytes - 1;
    REQUIRE(sx_table_create(&t, p, &cap, &measured) == SX_LIMIT && t == NULL);
    REQUIRE(measured.reason == SX_T_TOTAL_BYTES);
    cap.max_table_bytes++;
    REQUIRE(sx_table_create(&t, p, &cap, &measured) == SX_OK);
    SxTable *before = t;
    const SxRat *value = sx_table_value(t, 0);
    size_t held = sx_table_bytes(t), blocks = sx_live_blocks();
    cap.max_table_bytes = switched.peak_table_bytes - 1;
    REQUIRE(sx_table_pivot(&t, 0, 0, 0, &cap, &measured) == SX_LIMIT);
    REQUIRE(measured.reason == SX_T_TOTAL_BYTES && t == before);
    REQUIRE(sx_table_bytes(t) == held && sx_table_value(t, 0) == value);
    REQUIRE(sx_live_blocks() == blocks && sx_table_check(t, NULL, NULL) == SX_OK);
    cap.max_table_bytes++;
    REQUIRE(sx_table_pivot(&t, 0, 0, 0, &cap, &measured) == SX_OK);
    REQUIRE(sx_table_check(t, NULL, NULL) == SX_OK);
    sx_table_destroy(t);
}

int main(void) {
    SxRat nums[4];
    const char *tokens[] = {"18446744073709551617", "-4294967297", "0", "1"};
    __mpz_struct flat[4];
    for (size_t i = 0; i < 4; ++i) {
        sx_rat_init(&nums[i]);
        REQUIRE(sx_rat_set(&nums[i], tokens[i], "1", NULL, NULL) == SX_OK);
        flat[i] = nums[i].num;
    }
    SxProblem p = {2,1,flat};
    budget_probe(&p);
    struct InequList last = {flat+2, NULL}, head = {flat, &last};
    SxTable *t = NULL;
    SxTableStats st;
    last.next = &last;
    REQUIRE(sx_table_create_qcp(&t, &head, 1, NULL, &st) == SX_INVALID);
    REQUIRE(st.reason == SX_T_CYCLE && !t && last.next == &last);
    last.next = NULL;
    REQUIRE(sx_table_create_qcp(&t, &head, 1, NULL, &st) == SX_OK);
    REQUIRE(head.next == &last && !last.next && head.coef == flat && last.coef == flat+2);
    REQUIRE(sx_table_rows(t) == 2);
    equals(sx_table_beta(t,1), "0/1");
    equals(sx_table_coefficient(t,1,0), "1/1");
    SxRat third;
    sx_rat_init(&third);
    REQUIRE(sx_rat_set(&third,"1","3",NULL,NULL) == SX_OK);
    REQUIRE(sx_table_move(&t,0,&third,NULL,NULL) == SX_OK);
    equals(sx_table_value(t,2),"1/3");
    equals(sx_table_value(t,1),"55340232216833687554/3");
    const SxRat *old_upper = sx_table_value(t,2);
    REQUIRE(sx_table_bounds(&t,0,NULL,old_upper,NULL,NULL) == SX_OK);
    equals(sx_table_upper(t,0),"1/3");
    SxTable *before=t;
    REQUIRE(sx_table_move(&t,0,sx_table_value(t,1),NULL,&st) == SX_INVALID);
    REQUIRE(st.reason == SX_T_BOUND && t == before);
    REQUIRE(sx_table_recompute(&t,NULL,NULL) == SX_OK);
    equals(sx_table_value(t,1),"55340232216833687554/3");
    sx_rat_clear(&third);
    REQUIRE(sx_table_check(t, NULL, NULL) == SX_OK);
    sx_table_destroy(t);
    for (size_t i = 0; i < 4; ++i) sx_rat_clear(&nums[i]);
    REQUIRE(sx_live_blocks() == 0);
    puts("Independent peak budget boundary, pivot rollback, QCP cycle and ownership passed.");
    return 0;
}
