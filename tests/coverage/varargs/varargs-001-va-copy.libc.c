// varargs-001-va-copy.libc.c
// Exercise va_copy path in impl_mem.ml (L2706-2721)
#include <stdarg.h>
int sum_twice(int count, ...) {
    va_list args, args_copy;
    va_start(args, count);
    va_copy(args_copy, args);
    int sum1 = 0;
    for (int i = 0; i < count; i++)
        sum1 += va_arg(args, int);
    va_end(args);
    int sum2 = 0;
    for (int i = 0; i < count; i++)
        sum2 += va_arg(args_copy, int);
    va_end(args_copy);
    if (sum1 != sum2) return -1;
    return sum1;
}
int main(void) {
    int result = sum_twice(3, 10, 20, 12);
    if (result != 42) return 1;
    return 0;
}
