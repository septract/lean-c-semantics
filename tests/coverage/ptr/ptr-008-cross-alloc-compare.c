// ptr-008-cross-alloc-compare.c
// Relational comparison of pointers to different objects.
// This is UB in strict C but exercises impl_mem.ml cross-allocation
// comparison code paths.
// Expected: exit 0 or 1 (result is unspecified)
int main(void) {
    int x;
    int y;
    return &x < &y;
}
