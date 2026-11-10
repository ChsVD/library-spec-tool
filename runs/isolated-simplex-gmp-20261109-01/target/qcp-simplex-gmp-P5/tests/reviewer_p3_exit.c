/* Test-only monotonic clock to expire, deterministically, on the last check. */
#define _POSIX_C_SOURCE 200809L
#include "sx_solver_contract.h"
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define CHECK(x) do { if (!(x)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x); exit(2); } } while (0)

static size_t calls, jump_at, clock_error_at;
struct InequList { mpz_ptr coef; struct InequList *next; };
int __wrap_clock_gettime(clockid_t id, struct timespec *out) {
    CHECK(id == CLOCK_MONOTONIC);
    ++calls;
    if (calls == clock_error_at) { errno=EIO; return -1; }
    out->tv_sec = 100;
    out->tv_nsec = jump_at && calls >= jump_at ? 9000000L : 0L;
    return 0;
}

static void empty_output(const SxResult *r) {
    CHECK(!r->witness_length && !r->witness && !r->conflict.present && !r->conflict.blockers);
}

static void exits(struct InequList *p, size_t n, SxQStatus expected) {
    SxSolverLimits l = {0}; l.max_milliseconds = 3;
    SxResult r;
    sx_result_init(&r);
    calls=jump_at=clock_error_at=0;
    sx_check_qcp(p,n,&l,&r);
    CHECK(r.error==SX_OK && r.rational_status==expected && calls>=2);
    size_t last_check = calls, last_alloc = r.stats.allocations, peak = r.stats.peak_bytes;
    CHECK(last_alloc && peak);
    sx_result_clear(&r);
    for (size_t i=0; i<2; ++i) {
        calls=0; jump_at=i ? last_check : 2;
        sx_check_qcp(p,n,&l,&r);
        CHECK(r.error==SX_OK && r.rational_status==SX_Q_UNKNOWN && r.integer_status==SX_Z_UNKNOWN);
        CHECK(r.reason==SX_REASON_TIME && r.diagnostic==SX_D_TIME);
        empty_output(&r); sx_result_clear(&r);
    }
    calls=jump_at=0; clock_error_at=1;
    sx_check_qcp(p,n,&l,&r);
    CHECK(r.error==SX_INTERNAL && r.diagnostic==SX_D_CLOCK && r.rational_status==SX_Q_NOT_RUN);
    empty_output(&r); sx_result_clear(&r);
    clock_error_at=calls=0; l.fail_at=last_alloc;
    sx_check_qcp(p,n,&l,&r);
    CHECK(r.error==SX_OOM && r.rational_status==SX_Q_NOT_RUN && r.integer_status==SX_Z_NOT_DECIDED);
    empty_output(&r); sx_result_clear(&r);
    l.fail_at=0; l.max_table_bytes=peak-1;
    sx_check_qcp(p,n,&l,&r);
    CHECK(r.error==SX_OK && r.rational_status==SX_Q_UNKNOWN && r.reason==SX_REASON_SPACE);
    empty_output(&r); sx_result_clear(&r);
    l.max_table_bytes=peak;
    sx_check_qcp(p,n,&l,&r); CHECK(r.error==SX_OK && r.rational_status==expected);
    sx_result_clear(&r);
}

int main(void) {
    unsigned int one=1;
    __mpz_struct entries[] = {{0,1,&one},{0,-1,&one},{0,0,NULL},{0,1,&one}};
    struct InequList positive = {entries,NULL}, tail_input = {entries+2,NULL};
    exits(&positive,1,SX_Q_FEASIBLE);
    positive.next=&tail_input;
    exits(&positive,1,SX_Q_UNSAT);
    SxResult r;
    sx_result_init(&r);
    sx_check_qcp(NULL,SIZE_MAX,NULL,&r);
    CHECK(r.error==SX_OK && r.rational_status==SX_Q_UNKNOWN && r.integer_status==SX_Z_UNKNOWN);
    CHECK(r.reason==SX_REASON_SIZE_OVERFLOW && r.diagnostic==SX_D_OVERFLOW);
    empty_output(&r); sx_result_clear(&r);
    struct InequList tail={entries+2,NULL}, head={entries,&tail};
    sx_check_qcp(&head,1,NULL,&r);
    CHECK(r.error==SX_OK && r.rational_status==SX_Q_UNSAT && r.conflict.present);
    CHECK(head.coef==entries && head.next==&tail && !tail.next);
    sx_result_clear(&r);
    tail.next=&tail;
    sx_check_qcp(&head,1,NULL,&r);
    CHECK(r.error==SX_INVALID && r.rational_status==SX_Q_NOT_RUN);
    empty_output(&r); sx_result_clear(&r);
    tail.next=NULL; head.next=NULL;
    sx_check_qcp(&head,1,NULL,&r);
    CHECK(r.error==SX_OK && r.rational_status==SX_Q_FEASIBLE && r.witness_length==1 && r.stats.verified_rows==1);
    sx_result_clear(&r);
    CHECK(sx_live_blocks()==0 && sx_runtime_live_bytes()==0);
    puts("Independent deadline at early/last checkpoint, clock error, final allocation failure, and exact budget checks passed on feasible and conflicting inputs.");
    return 0;
}
