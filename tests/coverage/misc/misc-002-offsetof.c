// Test: offsetof exercises offsetof_ival in impl_mem.ml
// Exercises: offsetof_ival path for computing struct member offsets.
#include <stddef.h>
struct S {
    char a;
    int b;
    char c;
    int d;
};
int main(void) {
    // offsetof should reflect padding
    int off_b = offsetof(struct S, b);
    int off_d = offsetof(struct S, d);
    // b should be at offset 4 (after padding), d at offset 12
    return (off_b >= 1 && off_d > off_b) ? 0 : 1;
}
