// Test abort() builtin - should return 127 (signal exit code)
#include <stdlib.h>

int main(void) {
    abort();
    return 0;  // never reached
}
