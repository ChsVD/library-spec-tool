#include "gmp/fme/fme_def.h"

typedef unsigned int size_t;
#define SIZE_MAX 4294967295U

/* Verified GMP-FME MiniGMP interfaces, restricted to the branches in use. */
void mpz_set_ui(mpz_ptr r, unsigned long x)
/*@
    With old x0
    Require x == x0 && 0 <= x0 && store_Z(r, old)
    Ensure store_Z(r, x0)
*/;

void mpz_set(mpz_ptr rop, mpz_srcptr op)
/*@ neq
    With old z
    Require store_Z(rop, old) * store_Z(op, z)
    Ensure store_Z(rop, z) * store_Z(op, z)
*/;

void mpz_mul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@ neq
    With old z1 z2
    Require store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
    Ensure store_Z(rop, z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/;

void mpz_addmul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@
    With old z1 z2
    Require store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
    Ensure store_Z(rop, old + z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/;

static void combine(mpz_ptr out, mpz_srcptr m, mpz_srcptr a,
                    mpz_srcptr n, mpz_srcptr b)
/*@ non_alias
    With M A N B O
    Require store_Z(out, O) * store_Z(m, M) * store_Z(a, A) *
            store_Z(n, N) * store_Z(b, B)
    Ensure store_Z(out, M * A + N * B) * store_Z(m, M) * store_Z(a, A) *
           store_Z(n, N) * store_Z(b, B)
*/
{
    if (a->_mp_size == 0) {
        if (b->_mp_size == 0)
            mpz_set_ui(out, 0);
        else
            mpz_mul(out, n, b);
        return;
    }
    /*@ Assert exists ptr msize cap,
        out == out@pre && m == m@pre && a == a@pre &&
        n == n@pre && b == b@pre &&
        m->_mp_size == msize && m->_mp_alloc == cap && m->_mp_d == ptr &&
        same_sign(M, msize) && Zabs(msize) <= cap &&
        ((msize != 1 && mpd_store_Z_compact(UINT_MOD, ptr, Zabs(M), Zabs(msize))) ||
         (msize == 1 && 1 <= M && M <= UINT_MAX && UIntArray::full(ptr, 1, cons(M, nil)))) *
        UIntArray::undef_seg(ptr, Zabs(msize), cap) *
        store_Z(out, O) * store_Z(a, A) * store_Z(n, N) * store_Z(b, B)
    */
    if (m->_mp_size == 1 && m->_mp_d[0] == 1)
        mpz_set(out, a);
    else
        /*@ Assert
            out == out@pre && m == m@pre && a == a@pre &&
            n == n@pre && b == b@pre &&
            store_Z(out, O) * store_Z(m, M) * store_Z(a, A) *
            store_Z(n, N) * store_Z(b, B)
        */
        mpz_mul(out, m, a);
    if (b->_mp_size != 0)
        mpz_addmul(out, n, b);
}
