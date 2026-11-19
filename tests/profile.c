#define _POSIX_C_SOURCE 200809L
#include "profile.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
/* Test-only, process-local instrumentation. Not a concurrent public API. */
static struct {
    unsigned long long begun, completed, calls[4];
    double start, seconds[4], scans, next_report;
    size_t rows, cols, initial_bits, table_bits, peak_table_bits, arithmetic_bits;
    double initial_density, density, peak_density;
    int phase, capture;
    unsigned long long remainder_calls, remainder_zero;
    double remainder_seconds;
    unsigned long long phase_calls[2][2], normalizations, reductions;
    double phase_seconds[2][2];
    unsigned long long gcd_one[2], gcd_kept[2], div_one[2], quotient_one[2];
    unsigned long long samples_seen[2][2][5];
} stats;
static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}
static size_t bits(mpz_srcptr z) {
    int len = z->_mp_size < 0 ? -z->_mp_size : z->_mp_size;
    if (!len) return 0;
    unsigned int top = z->_mp_d[len - 1];
    size_t b = (size_t)(len - 1) * 32;
    while (top) { ++b; top >>= 1; }
    return b;
}
void sx_profile_reset(void) { memset(&stats, 0, sizeof(stats)); stats.start = now(); stats.phase = 1; stats.capture = getenv("SX_PROFILE_OPERANDS") != NULL; }
void sx_profile_begin(void) { ++stats.begun; }
static void emit(const char *stage, int answer) {
    fprintf(stderr, "sx_profile={\"stage\":\"%s\",\"answer\":%d,\"begun\":%llu,\"completed\":%llu,\"rows\":%zu,\"cols\":%zu,\"initial_bits\":%zu,\"table_bits\":%zu,\"peak_table_bits\":%zu,\"arithmetic_bits\":%zu,\"initial_density\":%.9f,\"density\":%.9f,\"peak_density\":%.9f,\"elapsed\":%.9f,\"scan_seconds\":%.9f,\"calls\":[%llu,%llu,%llu,%llu],\"seconds\":[%.9f,%.9f,%.9f,%.9f]",
        stage, answer, stats.begun, stats.completed, stats.rows, stats.cols,
        stats.initial_bits, stats.table_bits, stats.peak_table_bits, stats.arithmetic_bits,
        stats.initial_density, stats.density, stats.peak_density, now()-stats.start, stats.scans,
        stats.calls[0], stats.calls[1], stats.calls[2], stats.calls[3],
        stats.seconds[0], stats.seconds[1], stats.seconds[2], stats.seconds[3]);
    fprintf(stderr, ",\"normalizations\":%llu,\"reductions\":%llu,\"phase_calls\":[[%llu,%llu],[%llu,%llu]],\"phase_seconds\":[[%.9f,%.9f],[%.9f,%.9f]],\"gcd_one\":[%llu,%llu],\"gcd_kept\":[%llu,%llu],\"div_one\":[%llu,%llu],\"quotient_one\":[%llu,%llu],\"remainder_calls\":%llu,\"remainder_zero\":%llu,\"remainder_seconds\":%.9f}\n",
        stats.normalizations, stats.reductions,
        stats.phase_calls[0][0], stats.phase_calls[0][1], stats.phase_calls[1][0], stats.phase_calls[1][1],
        stats.phase_seconds[0][0], stats.phase_seconds[0][1], stats.phase_seconds[1][0], stats.phase_seconds[1][1],
        stats.gcd_one[0], stats.gcd_one[1], stats.gcd_kept[0], stats.gcd_kept[1],
        stats.div_one[0], stats.div_one[1], stats.quotient_one[0], stats.quotient_one[1], stats.remainder_calls, stats.remainder_zero, stats.remainder_seconds);
    fflush(stderr);
    stats.next_report = now() + 5;
}
void sx_profile_table(size_t rows, size_t cols, mpz_srcptr d, mpz_srcptr c,
                      mpz_srcptr a, const size_t *row, int initial) {
    double start = now(); size_t maximum = 0, nz = 0;
    stats.rows = rows; stats.cols = cols;
    for (size_t r = 0; r < rows; ++r) {
        size_t b = bits(d+r); if (b > maximum) maximum = b;
        b = bits(c+r); if (b > maximum) maximum = b;
        for (size_t v = 0; v < cols; ++v) {
            if (row[v] != SIZE_MAX) continue;
            b = bits(a+r*cols+v); nz += b != 0;
            if (b > maximum) maximum = b;
        }
    }
    stats.table_bits = maximum;
    if (maximum > stats.peak_table_bits) stats.peak_table_bits = maximum;
    stats.density = rows && cols > rows ? (double)nz / ((double)rows*(cols-rows)) : 0;
    if (stats.density > stats.peak_density) stats.peak_density = stats.density;
    if (initial) { stats.initial_bits = maximum; stats.initial_density = stats.density; }
    else ++stats.completed;
    stats.scans += now()-start;
    unsigned long long k = stats.completed;
    if (initial || (k && ((k & (k-1)) == 0 || k % 64 == 0))) emit(initial ? "initial" : "checkpoint", -1);
}
void sx_profile_finish(int answer) { emit("final", answer); }
void sx_profile_normalize_begin(void) { stats.phase = 0; ++stats.normalizations; }
void sx_profile_normalize_end(int reduced) { stats.reductions += reduced != 0; stats.phase = 1; }
static int unit(mpz_srcptr z) { return (z->_mp_size == 1 || z->_mp_size == -1) && z->_mp_d[0] == 1; }
static int equal_abs(mpz_srcptr x, mpz_srcptr y) {
    int a=x->_mp_size<0 ? -x->_mp_size : x->_mp_size;
    int b=y->_mp_size<0 ? -y->_mp_size : y->_mp_size;
    if (a!=b) return 0;
    for (int i=0; i<a; ++i) if (x->_mp_d[i]!=y->_mp_d[i]) return 0;
    return 1;
}
static void hex(mpz_srcptr z) {
    int n=z->_mp_size<0 ? -z->_mp_size : z->_mp_size;
    fprintf(stderr, "\"%s0x", z->_mp_size<0 ? "-" : "");
    if (!n) fputc('0', stderr);
    for (int i=n; i>0; --i) fprintf(stderr, "%08x", z->_mp_d[i-1]);
    fputc('"', stderr);
}
static void observe(int operation, mpz_srcptr a, mpz_srcptr b, mpz_srcptr result, double seconds) {
    int phase=stats.phase;
    ++stats.phase_calls[phase][operation]; stats.phase_seconds[phase][operation]+=seconds;
    if (!operation) { stats.gcd_one[phase]+=unit(result); stats.gcd_kept[phase]+=equal_abs(a,result); }
    else { stats.div_one[phase]+=unit(b); stats.quotient_one[phase]+=unit(result); }
    if (!stats.capture) return;
    size_t width=bits(a), other=bits(b); if (other>width) width=other;
    int bucket=width<=32 ? 0 : width<=256 ? 1 : width<=1024 ? 2 : width<=4096 ? 3 : 4;
    unsigned long long count=++stats.samples_seen[phase][operation][bucket];
    /* Stratified diagnostic samples, not a statistically weighted timing sample. */
    if (count>4 && (count & (count-1))) return;
    fprintf(stderr, "sx_operand={\"phase\":%d,\"operation\":%d,\"bucket\":%d,\"seen\":%llu,\"a\":",phase,operation,bucket,count);
    hex(a); fputs(",\"b\":",stderr); hex(b); fputs(",\"result\":",stderr); hex(result); fputs("}\n",stderr);
}
#define WRAPPER(name, index) \
void sx_profile_##name(mpz_ptr out, mpz_srcptr a, mpz_srcptr b) { \
    double start = now(); mpz_##name(out, a, b); \
    double elapsed=now()-start; stats.seconds[index] += elapsed; ++stats.calls[index]; \
    if (index==0 || index==2) observe(index==2, a, b, out, elapsed); \
    size_t width = bits(out); if (width > stats.arithmetic_bits) stats.arithmetic_bits = width; \
    if ((stats.calls[index] & 4095) == 0 && now() >= stats.next_report) emit("arithmetic", -1); \
}
WRAPPER(gcd, 0)
WRAPPER(mul, 1)
WRAPPER(divexact, 2)
WRAPPER(addmul, 3)

void mpz_tdiv_r(mpz_ptr, mpz_srcptr, mpz_srcptr);
void sx_profile_tdiv_r(mpz_ptr out, mpz_srcptr a, mpz_srcptr b) {
    double start=now();
    mpz_tdiv_r(out,a,b);
    stats.remainder_seconds+=now()-start;
    ++stats.remainder_calls;
    stats.remainder_zero+=out->_mp_size==0;
    size_t width=bits(out); if(width>stats.arithmetic_bits) stats.arithmetic_bits=width;
    if ((stats.remainder_calls & 4095)==0 && now()>=stats.next_report) emit("arithmetic",-1);
}
