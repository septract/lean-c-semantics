// libc-003-realloc.c
// realloc to larger size preserves old data.
// Exercises: impl_mem.ml realloc path (allocate new, copy, free old)
#include <stdlib.h>

int main(void) {
    int *p = malloc(2 * sizeof(int));
    if (!p) return 1;
    p[0] = 10;
    p[1] = 20;
    int *q = realloc(p, 4 * sizeof(int));
    if (!q) return 1;
    int ok = (q[0] == 10 && q[1] == 20);
    free(q);
    return ok ? 0 : 1;
}
