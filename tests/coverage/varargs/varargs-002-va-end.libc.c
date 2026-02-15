// varargs-002-va-end.libc.c
// Exercise va_end path in impl_mem.ml (L2743-2754)
#include <stdarg.h>
int first_arg(int count, ...) {
    va_list args;
    va_start(args, count);
    int first = va_arg(args, int);
    va_end(args); // explicit va_end
    return first;
}
int main(void) {
    if (first_arg(3, 42, 0, 0) != 42) return 1;
    return 0;
}
