// Test: size_t gets normalized to unsigned long in Core IR
// Cerberus normalizes size_t before emitting Core, so are_compatible
// sees unsigned long == unsigned long (structural equality works)
#include <stddef.h>

int foo(unsigned long n) {
    return (int)n;
}

int main(void) {
    size_t sz = 42;
    return foo(sz);  // Expected: 42
}
