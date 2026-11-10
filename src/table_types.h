#ifndef SX_TABLE_TYPES_H
#define SX_TABLE_TYPES_H

#include "runtime_scope.h"
#include "sx_table.h"

struct SxTable {
    size_t m, n, total, rat_count, original_count, coefficient_count;
    SxRat *rats, *original, *beta, *coeff, *value, *lower, *upper;
    size_t *indices, *basic, *nonbasic, *row, *column;
    unsigned char *flags;
};

typedef struct {
    SxScope scope;
    SxLimits arith;
    SxError error;
    SxTableReason reason;
    SxArithReason ar;
} Work;

typedef enum { MUT_BOUNDS, MUT_MOVE, MUT_PIVOT, MUT_RECOMPUTE } Mutation;

#endif
