// ptr3-002-int-to-ptr-null.libc.c
// Exercise ptrfromint null path in impl_mem.ml
#include <stdint.h>
#include <stddef.h>
int main(void) {
    intptr_t x = 0;
    int *p = (int*)x;     // integer 0 -> null pointer
    if (p != NULL) return 1;
    return 0;
}
