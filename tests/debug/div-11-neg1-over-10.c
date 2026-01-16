// Simplest test: -1 / 10 should be 0
#include <stdlib.h>

int main(void) {
    int x = -1;
    int result = x / 10;
    // -1 / 10 truncates towards zero, giving 0
    if (result != 0)
        abort();
    return 0;
}
