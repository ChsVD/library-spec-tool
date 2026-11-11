/* Simplex/QCP signed-int32 profile only; not a complete ISO C limits.h.
 * Requires the independently checked 32-bit signed int model.
 * Values match QCP IntLib / CompCert Int; no algorithm is modified.
 */
#ifndef QCP_SIMPLEX_INT32_LIMITS_H
#define QCP_SIMPLEX_INT32_LIMITS_H
#define INT_MAX 2147483647
#define INT_MIN (-2147483647 - 1)
#endif
