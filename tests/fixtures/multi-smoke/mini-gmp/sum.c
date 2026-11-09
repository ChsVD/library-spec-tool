/* SYNTHETIC REFERENCE: not mini-gmp or GNU GMP code.
 * This fixture contains only this module. Prefix sum over unsigned words.
 * a points to n readable unsigned values; n == 0 allows a == NULL.
 * Return is the mathematical sum modulo UINT_MAX+1. No proof is supplied.
 * Candidate mathematical observation, NOT a proved lemma: extending a
 * prefix by one word adds that word modulo UINT_MAX+1.
 * No writes, allocation, external calls or other source dependencies.
 * Build configuration and unsigned width are unspecified. */
#include <stddef.h>
unsigned prefix_sum(const unsigned *a, size_t n) {
    unsigned result = 0;
    while (n != 0) { --n; result += a[n]; }
    return result;
}
