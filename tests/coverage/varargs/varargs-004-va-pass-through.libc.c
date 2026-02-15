// varargs-004-va-pass-through.libc.c
// Exercise va_list as function parameter (L2756-2764)
#include <stdarg.h>
int sum_va(int count, va_list args) {
    int total = 0;
    for (int i = 0; i < count; i++)
        total += va_arg(args, int);
    return total;
}
int outer(int count, ...) {
    va_list args;
    va_start(args, count);
    int result = sum_va(count, args);
    va_end(args);
    return result;
}
int main(void) {
    if (outer(4, 10, 20, 5, 7) != 42) return 1;
    return 0;
}
