// Test casting -1 to pointer and comparing
#include <stdlib.h>
#include <stddef.h>

int main(void) {
    void *p = (void *)(size_t)-1;
    if (p != (void *)(size_t)-1)
        abort();
    return 0;
}
