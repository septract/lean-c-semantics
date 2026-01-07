// Test: compute out-of-bounds pointer and dereference
// Expected: UB (dereferencing one-past-end)
int a[10];
int main(void) {
    int *p = &a[10];  // one-past-end
    return *p;        // UB: deref one-past-end
}
