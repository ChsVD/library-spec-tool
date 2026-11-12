#include "backend.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
int mpz_cmp(mpz_srcptr, mpz_srcptr);
int main(void) {
    size_t m, n;
    while (scanf("%zu %zu", &m, &n) == 2) {
        struct InequList *rows = malloc(m * sizeof(*rows));
        mpz_ptr original = malloc(m * (n + 1) * sizeof(*original));
        for (size_t i = 0; i < m; i++) {
            rows[i].coef = malloc((n + 1) * sizeof(*rows[i].coef));
            rows[i].next = i + 1 < m ? rows + i + 1 : NULL;
            for (size_t j = 0; j <= n; j++) {
                char text[1024];
                assert(scanf("%1023s", text) == 1);
                mpz_ptr z = rows[i].coef + j;
                mpz_t ten, digit, tmp;
                mpz_init(z); mpz_init(ten); mpz_init(digit); mpz_init(tmp);
                mpz_set_ui(ten, 10);
                size_t k = text[0] == '-' ? 1 : 0;
                for (; text[k]; k++) {
                    assert(text[k] >= '0' && text[k] <= '9');
                    mpz_mul(tmp, z, ten);
                    mpz_set_ui(digit, (unsigned long)(text[k] - '0'));
                    mpz_t one;
                    mpz_init(one); mpz_set_ui(one, 1);
                    mpz_addmul(tmp, digit, one); mpz_set(z, tmp);
                    mpz_clear(one);
                }
                if (text[0] == '-') { mpz_neg(tmp, z); mpz_set(z, tmp); }
                mpz_init(original + i * (n + 1) + j);
                mpz_set(original + i * (n + 1) + j, z);
                mpz_clear(ten); mpz_clear(digit); mpz_clear(tmp);
            }
        }
        int answer = sx_check_qcp(m ? rows : NULL, n);
        assert(answer == 0 || answer == 1);
        for (size_t i = 0; i < m; i++) {
            assert(rows[i].next == (i + 1 < m ? rows + i + 1 : NULL));
            for (size_t j = 0; j <= n; j++) {
                assert(mpz_cmp(rows[i].coef + j, original + i * (n + 1) + j) == 0);
                mpz_clear(rows[i].coef + j);
                mpz_clear(original + i * (n + 1) + j);
            }
            free(rows[i].coef);
        }
        free(original); free(rows);
        printf("%d\n", answer);
    }
    return 0;
}