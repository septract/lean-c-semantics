// ptr3-001-funcptr-to-int.libc.c
// Exercise intfromptr PVfunction case in impl_mem.ml (L2443-2444)
#include <stdint.h>
int foo(void) { return 42; }
int main(void) {
    uintptr_t x = (uintptr_t)&foo; // function pointer to integer
    if (x == 0) return 1; // function pointer should be non-null
    return 0;
}
