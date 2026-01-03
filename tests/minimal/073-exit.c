// Test exit() builtin - should return 42
#include <stdlib.h>

int main(void) {
    exit(42);
    return 0;  // never reached
}
