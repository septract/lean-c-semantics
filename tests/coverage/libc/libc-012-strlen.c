// libc-012-strlen.c
// strlen returns the length of a string.
// Exercises: impl_mem.ml strlen path (byte-by-byte scan)
#include <string.h>

int main(void) {
    if (strlen("hello") != 5) return 1;
    if (strlen("") != 0) return 2;
    return 0;
}
