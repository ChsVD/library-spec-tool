typedef unsigned long long BN_ULONG;
typedef struct bignum_st {
  BN_ULONG *d;
  int top;
  int dmax;
  int neg;
  int flags;
} BIGNUM;
int bn_top_probe(BIGNUM *p)
/*@ With t Require store(&(p->top), t)
    Ensure __return == t && store(&(p->top), t) */
{ return p->top; }

BN_ULONG bn_limb_probe(BN_ULONG *p)
/*@ With x Require store(p, x)
    Ensure __return == x && store(p, x) */
{ return *p; }
BN_ULONG *bn_data_probe(BIGNUM *p)
/*@ With d Require store(&(p->d), d)
    Ensure __return == d && store(&(p->d), d) */
{ return p->d; }

int bn_dmax_probe(BIGNUM *p)
/*@ With x Require store(&(p->dmax), x)
    Ensure __return == x && store(&(p->dmax), x) */
{ return p->dmax; }

int bn_neg_probe(BIGNUM *p)
/*@ With x Require store(&(p->neg), x)
    Ensure __return == x && store(&(p->neg), x) */
{ return p->neg; }

int bn_flags_probe(BIGNUM *p)
/*@ With x Require store(&(p->flags), x)
    Ensure __return == x && store(&(p->flags), x) */
{ return p->flags; }
