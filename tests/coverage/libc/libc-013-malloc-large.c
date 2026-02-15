// libc-013-malloc-large.c
// Large malloc allocation, store at boundaries, free.
// Exercises: impl_mem.ml allocate_object with large size
#include <stdlib.h>

int main(void) {
    int n = 1024 * 1024;
    char *p = malloc(n);
    if (!p) return 1;
    p[0] = 'A';
    p[n - 1] = 'Z';
    int ok = (p[0] == 'A' && p[n - 1] == 'Z');
    free(p);
    return ok ? 0 : 1;
}
