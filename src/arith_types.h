#ifndef SX_ARITH_TYPES_H
#define SX_ARITH_TYPES_H

#include "sx_arith.h"
#include <setjmp.h>
#include <stddef.h>

typedef union Block Block;
union Block {
    max_align_t align;
    struct {
        Block *prev, *next;
        size_t bytes;
        int attached;
    } h;
};

typedef struct {
    jmp_buf jump;
    Block *head;
    size_t live, peak, attempt, maxbytes, maxlimbs, fail;
    SxError error;
    SxArithReason reason;
} Tx;

typedef union {
    max_align_t align;
    size_t bytes;
} Storage;

#endif
