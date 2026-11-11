#ifndef ECC_CONSTANTS_H
#define ECC_CONSTANTS_H

#include "dataType.h"

/* Verbatim file-scope constants from YCrypt/sm2/ecc_montg.c. */
static const UINT64 BN_ZERO[4] = { 0, 0, 0, 0 };

static const UINT64 MONTG_ONE[4] = {
	0x0000000000000001,
	0x00000000ffffffff,
	0x0000000000000000,
	0x0000000100000000
};

#endif
