// libc-008-memcpy-basic.c
// memcpy an int array and verify contents.
// Exercises: impl_mem.ml memcpy path
#include <string.h>

int main(void) {
    int src[4] = {1, 2, 3, 4};
    int dst[4];
    memcpy(dst, src, sizeof(src));
    for (int i = 0; i < 4; i++) {
        if (dst[i] != src[i]) return 1;
    }
    return 0;
}
