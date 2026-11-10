#include "sx_arith.h"
#include <limits.h>
#include <setjmp.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
void mpz_init(mpz_ptr);
void mpz_set(mpz_ptr, mpz_srcptr);
void mpz_set_ui(mpz_ptr, unsigned long);
void mpz_add(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_sub(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_mul(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_gcd(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_divexact(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_abs(mpz_ptr, mpz_srcptr);
void mpz_neg(mpz_ptr, mpz_srcptr);
int mpz_cmp(mpz_srcptr, mpz_srcptr);
