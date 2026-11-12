#ifndef SX_BACKEND_H
#define SX_BACKEND_H
#include "sx_solver.h"
void mpz_init(mpz_ptr);
void mpz_clear(mpz_ptr);
void mpz_set(mpz_ptr, mpz_srcptr);
void mpz_set_ui(mpz_ptr, unsigned long);
void mpz_set_si(mpz_ptr, long);
void mpz_neg(mpz_ptr, mpz_srcptr);
void mpz_abs(mpz_ptr, mpz_srcptr);
void mpz_mul(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_addmul(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_gcd(mpz_ptr, mpz_srcptr, mpz_srcptr);
void mpz_divexact(mpz_ptr, mpz_srcptr, mpz_srcptr);
#endif
