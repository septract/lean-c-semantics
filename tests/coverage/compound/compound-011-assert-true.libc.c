// compound-011-assert-true.libc.c
// Exercise assert() translation in translation.ml (L2697-2718)
#include <assert.h>
int main(void) {
    assert(1);
    int x = 42;
    assert(x == 42);
    assert(x > 0);
    return 0;
}
