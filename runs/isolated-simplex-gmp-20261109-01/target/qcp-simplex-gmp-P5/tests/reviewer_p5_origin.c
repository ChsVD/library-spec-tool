/* Separate caller translation unit. The source audit compiles this with the
 * original QCP fme_def.h. The portable run uses its bundled integer layout. */
#ifdef REVIEW_ORIGINAL_QCP
#include "gmp/fme/fme_def.h"
#else
#include "gmp/minigmp/gmp_def.h"
#endif
#include <stddef.h>
#include <stdlib.h>

struct InequList { mpz_ptr coef; struct InequList *next; };

static struct InequList *head;

/* Construct 1-Mx <= 0 and -1+Mx <= 0 with M=2^65+1. */
const struct InequList *reviewer_make_rows(void) {
    for (int i=1; i>=0; --i) {
        struct InequList *node=calloc(1,sizeof(*node));
        if (!node) abort();
        node->next=head;
        head=node;
        node->coef=calloc(2,sizeof(*node->coef));
        if (!node->coef) abort();
        for (int j=0; j<2; ++j) {
            mpz_ptr z=&node->coef[j];
            z->_mp_alloc=j ? 3 : 1;
            z->_mp_size=(i==j ? 1 : -1)*z->_mp_alloc;
            z->_mp_d=calloc((size_t)z->_mp_alloc,sizeof(*z->_mp_d));
            if (!z->_mp_d) abort();
            z->_mp_d[0]=1;
            if (j) z->_mp_d[2]=2;
        }
    }
    return head;
}

int reviewer_check_and_free_rows(void) {
    int ok=head && head->next && !head->next->next;
    for (int i=0; head; ++i) {
        struct InequList *node=head;
        head=node->next;
        for (int j=0; j<2; ++j) {
            mpz_ptr z=&node->coef[j];
            int limbs=j ? 3 : 1;
            ok=ok && z->_mp_alloc==limbs && z->_mp_size==(i==j ? 1 : -1)*limbs && z->_mp_d[0]==1;
            if (j) ok=ok && z->_mp_d[1]==0 && z->_mp_d[2]==2;
            free(z->_mp_d);
        }
        free(node->coef);
        free(node);
    }
    return ok;
}
