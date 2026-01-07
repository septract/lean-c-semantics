// Test: compute out-of-bounds pointer but don't dereference
// Expected: no UB (pointer arithmetic without deref is allowed)
int a[10];
int main(void) {
    int *p = &a[10];  // one-past-end is valid
    (void)p;
    return 0;
}
