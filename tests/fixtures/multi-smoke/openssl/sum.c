/* SYNTHETIC TARGET: not OpenSSL code.
 * This fixture contains only this module. Goal: sum an array of unsigned words.
 * a points to n readable unsigned values; n == 0 allows a == NULL.
 * Return is the mathematical sum modulo UINT_MAX+1. No proof is supplied.
 * No writes, allocation, external calls or other source dependencies.
 * Build configuration and unsigned width are unspecified. */
#include <stddef.h>
unsigned sum_words(const unsigned *a, size_t n) {
    unsigned sum = 0;
    for (size_t i = 0; i < n; ++i) sum += a[i];
    return sum;
}
