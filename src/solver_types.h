#ifndef SX_SOLVER_TYPES_H
#define SX_SOLVER_TYPES_H

#include "runtime_scope.h"
#include "sx_solver_contract.h"
#include "sx_table.h"

typedef struct {
    const struct InequList *head;
    size_t rows, variables;
} Source;

typedef struct {
    int enabled;
    size_t rows, variables, *rowmap, *colmap;
    unsigned char *used;
    SxRat *scales, *coefficients, unit, contradiction;
    size_t scales_initialized, coefficients_initialized, contradiction_row;
    __mpz_struct *view;
    SxProblem problem;
} Prepared;

typedef struct {
    SxScope scope;
    SxSolverLimits limits;
    SxResult result;
    SxTable *table;
    Prepared prep;
    SxError error;
    SxReason reason;
    SxDiagnostic diagnostic;
    SxArithReason arithmetic_reason;
} Solve;

#endif
