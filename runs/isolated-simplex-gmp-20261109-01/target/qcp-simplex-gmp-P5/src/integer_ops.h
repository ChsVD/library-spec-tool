#ifndef SX_INTEGER_OPS_H
#define SX_INTEGER_OPS_H
#include "sx_arith.h"
/* Private, integer-only operations, preserving the ordinary transaction rules.
   Exact division precondition is established by the preprocessing gcd. */
SxError sx_integer_gcd(SxRat *, const SxRat *, const SxRat *, const SxLimits *, SxStats *);
SxError sx_integer_divexact(SxRat *, const SxRat *, const SxRat *, const SxLimits *, SxStats *);
#endif
