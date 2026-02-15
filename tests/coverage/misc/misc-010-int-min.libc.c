// misc-010-int-min.libc.c
// Exercise IConstantMin in translation.ml (L205-206)
// Use INT_MIN / LONG_MIN constants
#include <limits.h>
int main(void) {
    int x = INT_MIN;
    if (x >= 0) return 1;
    long y = LONG_MIN;
    if (y >= 0) return 2;
    return 0;
}
