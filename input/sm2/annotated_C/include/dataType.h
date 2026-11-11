#ifndef DATATYPE_H
#define DATATYPE_H

typedef unsigned long long u8;
typedef unsigned long long UINT64;
typedef unsigned int       u4;
typedef unsigned short     u2;
typedef unsigned char      u1;
typedef signed char        int8_t;

/* Verification-side replacements for the standard-header aliases used by
 * the YCrypt source. */
typedef _Bool              bool;
typedef unsigned long long size_t;

/* Verification-side replacements for <stdbool.h>. */
#define false 0
#define true 1

typedef struct u32
{
	u8 v[4];
} u32;

typedef struct AFPoint
{
	u32 x;
	u32 y;
} AFPoint;

typedef struct JPoint
{
	u32 x;
	u32 y;
	u32 z;
} JPoint;

typedef struct SM2SIG
{
	u32 r;
	u32 s;
} SM2SIG;

typedef struct PrivKey
{
	u32 da;
} PrivKey;

typedef AFPoint PubKey;

/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib
 */

/*@ Extern Coq
      (U32_MOD : Z)
      (U64_MOD : Z)
      (U256_MOD : Z)
      (U512_MOD : Z)
      (Zmod : Z -> Z -> Z)
      (U64_POW : Z -> Z)
      (u256_of_limbs : Z -> Z -> Z -> Z -> Z)
      (u64_list_value : list Z -> Z)
      (u64_list_bounded : list Z -> Prop)
      (u32_list_value : list Z -> Z)
      (u32_list_bounded : list Z -> Prop)
      (store_u256_limbs : Z -> Z -> Assertion)
      (store_u64_limbs : Z -> Z -> Z -> Assertion)
      (store_u256 : Z -> Z -> Assertion)
 */

#endif
