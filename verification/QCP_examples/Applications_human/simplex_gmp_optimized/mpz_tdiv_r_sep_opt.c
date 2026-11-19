#include "gmp/minigmp/gmp_def.h"

enum mpz_div_round_mode { GMP_DIV_FLOOR, GMP_DIV_CEIL, GMP_DIV_TRUNC };

/*@ Import Coq Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.mpz_tdiv_r_sep_opt_lib */
/*@ Extern Coq (Z::rem : Z -> Z -> Z) */

/* Allows q or r to be zero. Returns 1 iff remainder is non-zero. */
int
mpz_div_qr(mpz_ptr q, mpz_ptr r,
           mpz_srcptr n, mpz_srcptr d, enum mpz_div_round_mode mode)
/*@ nonalias
  With q0 r0 n0 d0 mode0 old_q old_r zn zd
  Require
    q == q0 &&
    r == r0 &&
    n == n0 &&
    d == d0 &&
    mode == mode0 &&
    zd != 0 &&
    mode0 == GMP_DIV_TRUNC &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, old_q) *
    optional_store_Z(r0, old_r)
  Ensure exists qv rv,
    mpz_div_qr_math(mode0, zn, zd, qv, rv) &&
    0 <= __return && __return <= 1 &&
    mpz_div_qr_ret_ok(__return, rv) &&
    store_Z(n0, zn) * store_Z(d0, zd) *
    optional_store_Z(q0, qv) *
    optional_store_Z(r0, rv)
*/
;

void
mpz_tdiv_r(mpz_ptr r, mpz_srcptr n, mpz_srcptr d)
/*@ separated_trunc
    With old zn zd
    Require r != 0 && zd != 0 &&
            store_Z(r, old) * store_Z(n, zn) * store_Z(d, zd)
    Ensure store_Z(r, Z::rem(zn, zd)) * store_Z(n, zn) * store_Z(d, zd)
*/
{
  /*@ Assert
        r == r@pre && n == n@pre && d == d@pre &&
        r != 0 && zd != 0 &&
        store_Z(r, old) * store_Z(n, zn) * store_Z(d, zd) *
        optional_store_Z(0, 0)
  */
  mpz_div_qr(0, r, n, d, GMP_DIV_TRUNC)
    ;
}
