// libc-011-memset.c
// memset to zero and to 0xFF, verify results.
// Exercises: impl_mem.ml memset path
#include <string.h>

int main(void) {
    unsigned char buf[8];
    memset(buf, 0, sizeof(buf));
    for (int i = 0; i < 8; i++) {
        if (buf[i] != 0) return 1;
    }
    memset(buf, 0xFF, sizeof(buf));
    for (int i = 0; i < 8; i++) {
        if (buf[i] != 0xFF) return 2;
    }
    return 0;
}
