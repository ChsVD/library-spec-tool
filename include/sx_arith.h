#ifndef SX_ARITH_H
#define SX_ARITH_H
#include "gmp/minigmp/gmp_def.h"
#include <stddef.h>
typedef enum { SX_OK = 0, SX_INVALID, SX_OOM, SX_LIMIT, SX_INTERNAL } SxError;
typedef struct {
    __mpz_struct num, den;
} SxRat;
typedef struct {
    size_t max_limbs, max_bytes, fail_at;
} SxLimits;
typedef enum {
    SX_AR_NONE,
    SX_AR_BAD_ARGUMENT,
    SX_AR_BAD_DECIMAL,
    SX_AR_ZERO_DENOMINATOR,
    SX_AR_DIV_ZERO,
    SX_AR_BYTES,
    SX_AR_LIMBS,
    SX_AR_SIZE_OVERFLOW,
    SX_AR_ALLOC,
    SX_AR_REENTRY,
    SX_AR_TIME,
    SX_AR_CLOCK
} SxArithReason;
typedef struct {
    size_t allocations, peak_bytes;
    SxArithReason reason;
} SxStats;
/* Owning objects: initialize once; no shallow copies; clear is idempotent.
   Arithmetic operands are canonical (positive denominator, coprime, zero = 0/1).
   Use init/set/import or a successful operation to construct them.
   All operands same thread, valid initialized objects; out may alias either input.
   Failure leaves out unchanged. Limits NULL selects defaults; zero means default.
   max_bytes bounds transaction payload, max_limbs bounds each backend buffer.
   SX_LIMIT is resource exhaustion, never a mathematical conclusion. */
void sx_rat_init(SxRat *q);
void sx_rat_clear(SxRat *q);
SxError sx_rat_set(SxRat *out, const char *num, const char *den, const SxLimits *, SxStats *);
SxError sx_rat_op(SxRat *out, char op, const SxRat *a, const SxRat *b, const SxLimits *, SxStats *);
SxError sx_rat_cmp(int *out, const SxRat *a, const SxRat *b, const SxLimits *, SxStats *);
/* Allocating decimal export follows same transaction/failure policy. Caller frees
   successful string with sx_string_free. Export format is num/den. */
SxError sx_rat_string(char **out, const SxRat *, const SxLimits *, SxStats *);
/* Deep copy of a borrowed compact project integer. Alloc=0 may denote static
   read-only limbs; caller guarantees readable storage of abs(size) limbs. */
SxError sx_rat_import(SxRat *, mpz_srcptr, const SxLimits *, SxStats *);
void sx_string_free(char *);
size_t sx_live_blocks(void);
/* Current thread explicitly owned runtime bytes, including P2 storage/headers. */
size_t sx_runtime_live_bytes(void);
#endif
