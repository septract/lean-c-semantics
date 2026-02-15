// ctrl3-001-malloc-computed-size.libc.c
// Exercise Alloc0 operand evaluation branch in core_reduction.ml (L813-819)
// Use a computed (non-literal) size for malloc
#include <stdlib.h>
int main(void) {
    int n = 10;
    int *p = malloc((unsigned long)n * sizeof(int));
    if (p == 0) return 1;
    for (int i = 0; i < n; i++)
        p[i] = i;
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += p[i];
    free(p);
    if (sum != 45) return 2; // 0+1+2+...+9 = 45
    return 0;
}
