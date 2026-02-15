// ptr-004-null-compare.c
// Compare pointer to NULL.
// Exercises: impl_mem.ml pointer-null comparison path
// Expected: exit 0
int main(void) {
    int x;
    int *p = &x;
    return p != 0 ? 0 : 1;
}
