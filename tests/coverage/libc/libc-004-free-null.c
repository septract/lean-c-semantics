// libc-004-free-null.c
// free(NULL) is a no-op per the C standard.
// Exercises: impl_mem.ml free with null pointer check
#include <stdlib.h>

int main(void) {
    free(NULL);
    return 0;
}
