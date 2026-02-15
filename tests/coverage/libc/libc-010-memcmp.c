// libc-010-memcmp.c
// memcmp: equal and unequal cases.
// Exercises: impl_mem.ml memcmp path
#include <string.h>

int main(void) {
    int a[3] = {1, 2, 3};
    int b[3] = {1, 2, 3};
    int c[3] = {1, 2, 4};
    if (memcmp(a, b, sizeof(a)) != 0) return 1;
    if (memcmp(a, c, sizeof(a)) == 0) return 2;
    return 0;
}
