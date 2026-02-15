// varargs-005-va-sum.libc.c
// Basic variadic function exercising va_start/va_arg/va_end cycle
#include <stdarg.h>
int sum(int count, ...) {
    va_list args;
    va_start(args, count);
    int total = 0;
    for (int i = 0; i < count; i++)
        total += va_arg(args, int);
    va_end(args);
    return total;
}
int main(void) {
    if (sum(1, 42) != 42) return 1;
    if (sum(2, 20, 22) != 42) return 2;
    if (sum(5, 1, 2, 3, 4, 32) != 42) return 3;
    return 0;
}
