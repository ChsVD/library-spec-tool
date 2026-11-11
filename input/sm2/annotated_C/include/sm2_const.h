#ifndef SM2_CONST_H
#define SM2_CONST_H

#include "dataType.h"

static const u32 SM2_P = {
	{ 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF00000000,
	  0xFFFFFFFFFFFFFFFF, 0xFFFFFFFEFFFFFFFF }
};

static const u32 SM2_inv2P = {
	{ 0x8000000000000000, 0xFFFFFFFF80000000,
	  0xFFFFFFFFFFFFFFFF, 0x7FFFFFFF7FFFFFFF }
};

static const u32 SM2_rhoP = {
	{ 0x0000000000000001, 0x00000000FFFFFFFF,
	  0x0000000000000000, 0x0000000100000000 }
};

/* R^2 mod P for R = 2^256. */
static const u32 SM2_H = {
	0x200000003L, 0x2ffffffffL, 0x100000001L, 0x400000002L
};

/* Short-Weierstrass coefficients for the SM2 curve. */
static const u32 SM2_a = {
	{ 0xFFFFFFFFFFFFFFFC, 0xFFFFFFFF00000000,
	  0xFFFFFFFFFFFFFFFF, 0xFFFFFFFEFFFFFFFF }
};

static const u32 SM2_b = {
	{ 0xDDBCBD414D940E93, 0xF39789F515AB8F92,
	  0x4D5A9E4BCF6509A7, 0x28E9FA9E9D9F5E34 }
};

/*
 * The original YCrypt sm2_const.h also provides the group order N, its
 * two's-complement correction rhoN, and the Montgomery low-limb inverse.
 * These constants are shared by basicOp and later source modules.
 */
static const u8 SM2_neg_invN = 3638801332807469429L;

static const u32 SM2_N = {
	{ 0x53BBF40939D54123, 0x7203DF6B21C6052B,
	  0xFFFFFFFFFFFFFFFF, 0xFFFFFFFEFFFFFFFF }
};

static const u32 SM2_rhoN = {
	{ 0xAC440BF6C62ABEDD, 0x8DFC2094DE39FAD4,
	  0x0000000000000000, 0x0000000100000000 }
};

static const u32 SM2_NH = {
	0x901192AF7C114F20, 0x3464504ADE6FA2FA,
	0x620FC84C3AFFE0D4, 0x1EB5E412A22B3D3B
};

/*@ Extern Coq
      (SM2_P_Z : Z)
      (SM2_N_Z : Z)
      (SM2_RHOP_Z : Z)
      (SM2_RHON_Z : Z)
      (SM2_RHOP0_Z : Z)
      (SM2_RHOP1_Z : Z)
      (SM2_RHOP2_Z : Z)
      (SM2_RHOP3_Z : Z)
      (SM2_H_Z : Z)
      (SM2_H0_Z : Z)
      (SM2_H1_Z : Z)
      (SM2_H2_Z : Z)
      (SM2_H3_Z : Z)
      (SM2_P_LIMB_0 : Z)
      (SM2_P_LIMB_1 : Z)
      (SM2_P_LIMB_2 : Z)
      (SM2_P_LIMB_3 : Z)
      (SM2_N0_Z : Z)
      (SM2_N1_Z : Z)
      (SM2_N2_Z : Z)
      (SM2_N3_Z : Z)
      (SM2_RHON0_Z : Z)
      (SM2_RHON1_Z : Z)
      (SM2_RHON2_Z : Z)
      (SM2_RHON3_Z : Z)
      (SM2_NH_Z : Z)
      (SM2_NH0_Z : Z)
      (SM2_NH1_Z : Z)
      (SM2_NH2_Z : Z)
      (SM2_NH3_Z : Z)
      (SM2_NEG_INV_N : Z)
      (SM2_NEG_INV_N_QUOTIENT : Z)
      (store_fp : Z -> Z -> Assertion)
      (store_fn : Z -> Z -> Assertion)
      (store_sm2_p : Assertion)
      (store_sm2_h : Assertion)
      (store_sm2_n : Assertion)
      (store_sm2_rhop : Assertion)
      (store_sm2_rhon : Assertion)
      (store_sm2_nh : Assertion)
      (store_sm2_neg_inv_n : Assertion)
 */

#endif
