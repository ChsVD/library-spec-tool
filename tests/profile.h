#ifndef SX_TEST_PROFILE_H
#define SX_TEST_PROFILE_H
#include "backend.h"
void sx_profile_normalize_begin(void);
void sx_profile_normalize_end(int);
void sx_profile_reset(void);
void sx_profile_begin(void);
void sx_profile_table(size_t, size_t, mpz_srcptr, mpz_srcptr, mpz_srcptr, const size_t *, int);
void sx_profile_finish(int);
void sx_profile_gcd(mpz_ptr, mpz_srcptr, mpz_srcptr);
void sx_profile_mul(mpz_ptr, mpz_srcptr, mpz_srcptr);
void sx_profile_divexact(mpz_ptr, mpz_srcptr, mpz_srcptr);
void sx_profile_tdiv_r(mpz_ptr, mpz_srcptr, mpz_srcptr);
void sx_profile_addmul(mpz_ptr, mpz_srcptr, mpz_srcptr);
#endif
