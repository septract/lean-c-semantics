// varargs-003-va-multiple-types.libc.c
// Exercise va_arg with different types
#include <stdarg.h>
long mixed_sum(int count, ...) {
    va_list args;
    va_start(args, count);
    int a = va_arg(args, int);
    long b = va_arg(args, long);
    int c = va_arg(args, int);
    va_end(args);
    return a + b + c;
}
int main(void) {
    long result = mixed_sum(3, 10, 20L, 12);
    if (result != 42) return 1;
    return 0;
}
