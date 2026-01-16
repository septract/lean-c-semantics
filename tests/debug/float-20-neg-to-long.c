// Test negative float to long conversion
#include <stdlib.h>

int main(void) {
    double d = -12.0;
    long l = (long) d;
    if (l != -12)
        abort();
    return 0;
}
