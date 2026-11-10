#include "sx_solver_contract.h"
#include <stdio.h>
#include <string.h>

extern const struct InequList *reviewer_make_rows(void);
extern int reviewer_check_and_free_rows(void);

int main(void) {
    SxResult r;
    sx_result_init(&r);
    sx_check_qcp(reviewer_make_rows(),1,NULL,&r);
    int ok=reviewer_check_and_free_rows();
    ok=ok && r.error==SX_OK && r.rational_status==SX_Q_FEASIBLE && r.integer_status==SX_Z_UNKNOWN;
    ok=ok && r.reason==SX_REASON_FRACTIONAL && r.stats.verified_rows==2 && r.witness_length==1;
    char *text=NULL;
    if (ok) ok=sx_rat_string(&text,r.witness,NULL,NULL)==SX_OK && strcmp(text,"1/36893488147419103233")==0;
    if (ok) printf("Borrowed QCP rows freed by caller; independent result x=%s\n",text);
    sx_string_free(text);
    sx_result_clear(&r);
    sx_result_clear(&r);
    return ok && sx_runtime_live_bytes()==0 ? 0 : 1;
}
