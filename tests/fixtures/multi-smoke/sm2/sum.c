/* SYNTHETIC REFERENCE: not SM2 code.
 * This fixture contains only this module. Sum exactly four unsigned values.
 * a must point to at least four readable unsigned values.
 * Return is the mathematical sum modulo UINT_MAX+1. No proof is supplied.
 * No writes, allocation, external calls or other source dependencies.
 * Fixed-size bound differs from a variable-length interface.
 * Build configuration and unsigned width are unspecified. */
unsigned sum_four(const unsigned *a) {
    return a[0] + a[1] + a[2] + a[3];
}
