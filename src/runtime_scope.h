#ifndef SX_RUNTIME_SCOPE_H
#define SX_RUNTIME_SCOPE_H
#include "sx_arith.h"
typedef struct SxScope {
    size_t baseline, initial, limit, peak, attempts, fail;
    SxError error;
    SxArithReason reason;
    struct SxScope *parent;
    int allow_children;
    unsigned long long started_ms, duration_ms;
} SxScope;
SxError sx_scope_begin(SxScope *, size_t initial, size_t limit, size_t fail);
SxError sx_scope_checkpoint(void);
SxError sx_scope_deadline(SxScope *, unsigned long long milliseconds);
void sx_scope_end(SxScope *);
void *sx_scope_alloc(size_t);
void sx_scope_free(void *);
size_t sx_scope_size(const void *);
size_t sx_rat_bytes(const SxRat *);
#endif
