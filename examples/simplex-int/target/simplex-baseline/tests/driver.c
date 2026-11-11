#include "../simplex.h"
#include <stdio.h>
#include <stdlib.h>

/* Test harness only; not part of the future QCP proof target. */
int main(int argc, char **argv) {
    struct SxState s;
    int c[SX_ROWS][SX_INPUT_VARS + 1] = {{0}};
    struct InequList nodes[SX_ROWS];
    int m, n, limit, i, j, result;
    if (scanf("%d%d%d", &m, &n, &limit) != 3) return 2;
    if (m < 0 || m > SX_ROWS || n < 0 || n > SX_INPUT_VARS) {
        printf("-1\n"); return 0;
    }
    for (i = 0; i < m; i++) {
        for (j = 0; j <= n; j++)
            if (scanf("%d", &c[i][j]) != 1) return 2;
        nodes[i].coef = c[i];
        nodes[i].next = i + 1 < m ? &nodes[i+1] : NULL;
    }
    if (argc > 1 && argv[1][0] == 'l')
        result = simplex_deduction(&s, m ? nodes : NULL, n, limit);
    else result = sx_check(&s, m, n, c, limit);
    printf("%d\n", result);
    if (result == SX_FEASIBLE) {
        for (j = 0; j < n; j++) printf("%d/%d\n", s.value[j].num, s.value[j].den);
    }
    return 0;
}
