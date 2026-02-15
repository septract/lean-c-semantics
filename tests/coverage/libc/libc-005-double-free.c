// libc-005-double-free.c
// Double free is undefined behavior.
// Exercises: impl_mem.ml kill on already-dead allocation
#include <stdlib.h>

int main(void) {
    int *p = malloc(sizeof(int));
    if (!p) return 1;
    free(p);
    free(p);  // UB: double free
    return 0;
}
