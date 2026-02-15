// libc-002-calloc.c
// calloc zeroes memory.
// Exercises: impl_mem.ml calloc path (allocate + zero-fill)
#include <stdlib.h>

int main(void) {
    int *p = calloc(5, sizeof(int));
    if (!p) return 1;
    for (int i = 0; i < 5; i++) {
        if (p[i] != 0) {
            free(p);
            return 1;
        }
    }
    free(p);
    return 0;
}
