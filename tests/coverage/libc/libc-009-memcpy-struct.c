// libc-009-memcpy-struct.c
// memcpy a struct from one location to another.
// Exercises: impl_mem.ml memcpy with struct-sized regions
#include <string.h>

struct point {
    int x;
    int y;
};

int main(void) {
    struct point a = {10, 20};
    struct point b;
    memcpy(&b, &a, sizeof(struct point));
    if (b.x != 10 || b.y != 20) return 1;
    return 0;
}
