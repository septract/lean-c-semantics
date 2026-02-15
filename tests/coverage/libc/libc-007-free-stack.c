// libc-007-free-stack.c
// Freeing a stack pointer is undefined behavior.
// Exercises: impl_mem.ml free with non-heap allocation
#include <stdlib.h>

int main(void) {
    int x = 5;
    free(&x);  // UB: freeing stack pointer
    return 0;
}
