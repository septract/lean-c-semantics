// Simpler test - just check if pointer comparison works
#include <stddef.h>

int main(void) {
    void *p = (void *)(size_t)-1;
    void *q = (void *)(size_t)-1;
    // Return 0 if equal, 1 if not
    return (p == q) ? 0 : 1;
}
