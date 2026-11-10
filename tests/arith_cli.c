#include "sx_arith.h"
#include <stdio.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc != 6 || strlen(argv[1]) != 1) {
        fprintf(stderr, "usage: arith_cli OP AN AD BN BD\n");
        return 2;
    }
    SxRat a, b, c;
    sx_rat_init(&a);
    sx_rat_init(&b);
    sx_rat_init(&c);
    SxError e = sx_rat_set(&a, argv[2], argv[3], NULL, NULL);
    if (!e)
        e = sx_rat_set(&b, argv[4], argv[5], NULL, NULL);
    if (!e) {
        if (argv[1][0] == 'c') {
            int x;
            e = sx_rat_cmp(&x, &a, &b, NULL, NULL);
            if (!e)
                printf("%d\n", x);
        } else {
            e = sx_rat_op(&c, argv[1][0], &a, &b, NULL, NULL);
            char *s = NULL;
            if (!e)
                e = sx_rat_string(&s, &c, NULL, NULL);
            if (!e) {
                puts(s);
                sx_string_free(s);
            }
        }
    }
    sx_rat_clear(&a);
    sx_rat_clear(&b);
    sx_rat_clear(&c);
    if (e)
        fprintf(stderr, "error=%d\n", e);
    if (sx_live_blocks())
        return 3;
    return e ? 1 : 0;
}
