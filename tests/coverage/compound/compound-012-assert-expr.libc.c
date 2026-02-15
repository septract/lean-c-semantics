// compound-012-assert-expr.libc.c
// Exercise assert() with complex expressions
#include <assert.h>
int main(void) {
    int a = 10, b = 20;
    assert(a + b == 30);
    assert(a < b);
    assert(!(a > b));
    return 0;
}
