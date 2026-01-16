// Test signed integer division with negative numbers
#include <stdlib.h>

int main(void) {
    // -10 / 10 should be -1
    int x = -10;
    int result = x / 10;
    if (result != -1)
        abort();
    return 0;
}
