// mem3-007-realloc-null.libc.c
// Exercise realloc NULL path in impl_mem.ml (L2668-2696)
#include <stdlib.h>
int main(void) {
    // realloc(NULL, n) should behave like malloc(n)
    int *p = realloc((void*)0, 4 * sizeof(int));
    if (p == 0) return 1;
    p[0] = 10;
    p[1] = 20;
    p[2] = 30;
    p[3] = 40;
    if (p[0] + p[1] + p[2] + p[3] != 100) return 2;
    free(p);
    return 0;
}
