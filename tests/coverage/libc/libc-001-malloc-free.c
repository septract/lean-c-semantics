// libc-001-malloc-free.c
// Basic malloc, store, load, free.
// Exercises: impl_mem.ml allocate_object, store, load, kill (free)
#include <stdlib.h>

int main(void) {
    int *p = malloc(sizeof(int));
    if (!p) return 1;
    *p = 42;
    int v = *p;
    free(p);
    return (v == 42) ? 0 : 1;
}
