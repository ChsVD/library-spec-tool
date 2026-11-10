#ifndef SX_TABLE_INTERNAL_H
#define SX_TABLE_INTERNAL_H
#include "sx_table.h"

/* QCP GMP FME row: borrowed coefficients, NULL-terminated list. */
struct InequList {
    mpz_ptr coef;
    struct InequList *next;
};

/* Private solver-to-table handoff, not a public independent entry.
   source_validate has established a finite acyclic list of exactly rows nodes,
   each with a non-NULL coef. The caller supplies variables+1 readable integer
   headers per row and readable limbs as required by integer import, and keeps
   all input storage unchanged throughout this call. rows==0
   requires head==NULL. This function does not recheck or recount the list.
   Integer import, arithmetic/size limits, allocation and invariants remain
   checked by the table layer. As for sx_table_create, requires *out==NULL. */
SxError sx_table_create_validated_list(SxTable **out, const struct InequList *head,
                                       size_t rows, size_t variables,
                                       const SxTableLimits *, SxTableStats *);
#endif
