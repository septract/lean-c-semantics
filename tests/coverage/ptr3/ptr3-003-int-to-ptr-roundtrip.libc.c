// ptr3-003-int-to-ptr-roundtrip.libc.c
// Exercise both intfromptr and ptrfromint paths
#include <stdint.h>
int main(void) {
    int x = 42;
    int *p = &x;
    uintptr_t addr = (uintptr_t)p;  // ptr to int
    int *q = (int*)addr;            // int to ptr
    if (*q != 42) return 1;
    return 0;
}
