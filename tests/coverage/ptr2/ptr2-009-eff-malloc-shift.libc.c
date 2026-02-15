// ptr2-009-eff-malloc-shift.libc.c
// Array shift on malloc'd memory via subscript operator.
// Exercises eff_array_shift_ptrval on heap-allocated storage.
// Requires libc (malloc/free).
// Expected return: 42
#include <stdlib.h>

int main(void) {
    int *p = malloc(10 * sizeof(int));
    if (!p) return 1;
    p[5] = 42;
    int r = p[5];
    free(p);
    return r;
}
