// libc-006-use-after-free.c
// Reading from freed memory is undefined behavior.
// Exercises: impl_mem.ml load on dead allocation
#include <stdlib.h>

int main(void) {
    int *p = malloc(sizeof(int));
    if (!p) return 1;
    *p = 99;
    free(p);
    int v = *p;  // UB: use after free
    return v;
}
