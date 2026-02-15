// libc-014-write-after-free.c
// Writing to freed memory is undefined behavior.
// Exercises: impl_mem.ml store on dead allocation
#include <stdlib.h>

int main(void) {
    int *p = malloc(sizeof(int));
    if (!p) return 1;
    *p = 42;
    free(p);
    *p = 99;  // UB: write after free
    return 0;
}
