// ptr-005-one-past-end-compare.c
// Compare one-past-end pointer (valid comparison, no deref).
// Exercises: impl_mem.ml one-past-end pointer comparison
// Expected: exit 0
int main(void) {
    int a[5];
    int *p = &a[5];
    return p == &a[5] ? 0 : 1;
}
